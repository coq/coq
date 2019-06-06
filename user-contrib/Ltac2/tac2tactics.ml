(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Globnames
open Tac2types
open Tac2extffi
open Genredexpr
open Proofview.Notations

let return = Proofview.tclUNIT
let thaw r f = Tac2ffi.app_fun1 f Tac2ffi.unit r ()

let tactic_infer_flags with_evar = {
  Pretyping.use_typeclasses = true;
  Pretyping.solve_unification_constraints = true;
  Pretyping.fail_evar = not with_evar;
  Pretyping.expand_evars = true;
  Pretyping.program_mode = false;
  Pretyping.polymorphic = false;
}

(** FIXME: export a better interface in Tactics *)
let delayed_of_tactic tac env sigma =
  let _, pv = Proofview.init sigma [] in
  let name, poly = Id.of_string "ltac2_delayed", false in
  let c, pv, _, _ = Proofview.apply ~name ~poly env tac pv in
  (sigma, c)

let delayed_of_thunk r tac env sigma =
  delayed_of_tactic (thaw r tac) env sigma

let mk_bindings = function
| ImplicitBindings l -> Tactypes.ImplicitBindings l
| ExplicitBindings l ->
  let l = List.map CAst.make l in
  Tactypes.ExplicitBindings l
| NoBindings -> Tactypes.NoBindings

let mk_with_bindings (x, b) = (x, mk_bindings b)

let rec mk_intro_pattern = function
| IntroForthcoming b -> CAst.make @@ Tactypes.IntroForthcoming b
| IntroNaming ipat -> CAst.make @@ Tactypes.IntroNaming (mk_intro_pattern_naming ipat)
| IntroAction ipat -> CAst.make @@ Tactypes.IntroAction (mk_intro_pattern_action ipat)

and mk_intro_pattern_naming = function
| IntroIdentifier id -> Namegen.IntroIdentifier id
| IntroFresh id -> Namegen.IntroFresh id
| IntroAnonymous -> Namegen.IntroAnonymous

and mk_intro_pattern_action = function
| IntroWildcard -> Tactypes.IntroWildcard
| IntroOrAndPattern ipat -> Tactypes.IntroOrAndPattern (mk_or_and_intro_pattern ipat)
| IntroInjection ipats -> Tactypes.IntroInjection (List.map mk_intro_pattern ipats)
| IntroApplyOn (c, ipat) ->
  let c = CAst.make @@ delayed_of_thunk Tac2ffi.constr c in
  Tactypes.IntroApplyOn (c, mk_intro_pattern ipat)
| IntroRewrite b -> Tactypes.IntroRewrite b

and mk_or_and_intro_pattern = function
| IntroOrPattern ipatss ->
  Tactypes.IntroOrPattern (List.map (fun ipat -> List.map mk_intro_pattern ipat) ipatss)
| IntroAndPattern ipats ->
  Tactypes.IntroAndPattern (List.map mk_intro_pattern ipats)

let mk_intro_patterns ipat = List.map mk_intro_pattern ipat

let mk_occurrences f = function
| AllOccurrences -> Locus.AllOccurrences
| AllOccurrencesBut l -> Locus.AllOccurrencesBut (List.map f l)
| NoOccurrences -> Locus.NoOccurrences
| OnlyOccurrences l -> Locus.OnlyOccurrences (List.map f l)

let mk_occurrences_expr occ =
  mk_occurrences (fun i -> Locus.ArgArg i) occ

let mk_hyp_location (id, occs, h) =
  ((mk_occurrences_expr occs, id), h)

let mk_clause cl = {
  Locus.onhyps = Option.map (fun l -> List.map mk_hyp_location l) cl.onhyps;
  Locus.concl_occs = mk_occurrences_expr cl.concl_occs;
}

let intros_patterns ev ipat =
  let ipat = mk_intro_patterns ipat in
  Tactics.intros_patterns ev ipat

let apply adv ev cb cl =
  let map c =
    let c = thaw constr_with_bindings c >>= fun p -> return (mk_with_bindings p) in
    None, CAst.make (delayed_of_tactic c)
  in
  let cb = List.map map cb in
  match cl with
  | None -> Tactics.apply_with_delayed_bindings_gen adv ev cb
  | Some (id, cl) ->
    let cl = Option.map mk_intro_pattern cl in
    Tactics.apply_delayed_in adv ev id cb cl

let mk_destruction_arg = function
| ElimOnConstr c ->
  let c = c >>= fun c -> return (mk_with_bindings c) in
  Tactics.ElimOnConstr (delayed_of_tactic c)
| ElimOnIdent id -> Tactics.ElimOnIdent CAst.(make id)
| ElimOnAnonHyp n -> Tactics.ElimOnAnonHyp n

let mk_induction_clause (arg, eqn, as_, occ) =
  let eqn = Option.map (fun ipat -> CAst.make @@ mk_intro_pattern_naming ipat) eqn in
  let as_ = Option.map (fun ipat -> CAst.make @@ mk_or_and_intro_pattern ipat) as_ in
  let occ = Option.map mk_clause occ in
  ((None, mk_destruction_arg arg), (eqn, as_), occ)

let induction_destruct isrec ev (ic : induction_clause list) using =
  let ic = List.map mk_induction_clause ic in
  let using = Option.map mk_with_bindings using in
  Tactics.induction_destruct isrec ev (ic, using)

let elim ev c copt =
  let c = mk_with_bindings c in
  let copt = Option.map mk_with_bindings copt in
  Tactics.elim ev None c copt

let generalize pl =
  let mk_occ occs = mk_occurrences (fun i -> i) occs in
  let pl = List.map (fun (c, occs, na) -> (mk_occ occs, c), na) pl in
  Tactics.new_generalize_gen pl

let general_case_analysis ev c =
  let c = mk_with_bindings c in
  Tactics.general_case_analysis ev None c

let constructor_tac ev n i bnd =
  let bnd = mk_bindings bnd in
  Tactics.constructor_tac ev n i bnd

let left_with_bindings ev bnd =
  let bnd = mk_bindings bnd in
  Tactics.left_with_bindings ev bnd

let right_with_bindings ev bnd =
  let bnd = mk_bindings bnd in
  Tactics.right_with_bindings ev bnd

let split_with_bindings ev bnd =
  let bnd = mk_bindings bnd in
  Tactics.split_with_bindings ev [bnd]

let specialize c pat =
  let c = mk_with_bindings c in
  let pat = Option.map mk_intro_pattern pat in
  Tactics.specialize c pat

let change pat c cl =
  let open Tac2ffi in
  Proofview.Goal.enter begin fun gl ->
  let c subst env sigma =
    let subst = Array.map_of_list snd (Id.Map.bindings subst) in
    delayed_of_tactic (Tac2ffi.app_fun1 c (array constr) constr subst) env sigma
  in
  let cl = mk_clause cl in
  Tactics.change ~check:true pat c cl
  end

let rewrite ev rw cl by =
  let map_rw (orient, repeat, c) =
    let c = c >>= fun c -> return (mk_with_bindings c) in
    (Option.default true orient, repeat, None, delayed_of_tactic c)
  in
  let rw = List.map map_rw rw in
  let cl = mk_clause cl in
  let by = Option.map (fun tac -> Tacticals.New.tclCOMPLETE (thaw Tac2ffi.unit tac), Equality.Naive) by in
  Equality.general_multi_rewrite ev rw cl by

let symmetry cl =
  let cl = mk_clause cl in
  Tactics.intros_symmetry cl

let forward fst tac ipat c =
  let ipat = Option.map mk_intro_pattern ipat in
  Tactics.forward fst tac ipat c

let assert_ = function
| AssertValue (id, c) ->
  let ipat = CAst.make @@ Tactypes.IntroNaming (Namegen.IntroIdentifier id) in
  Tactics.forward true None (Some ipat) c
| AssertType (ipat, c, tac) ->
  let ipat = Option.map mk_intro_pattern ipat in
  let tac = Option.map (fun tac -> thaw Tac2ffi.unit tac) tac in
  Tactics.forward true (Some tac) ipat c

let letin_pat_tac ev ipat na c cl =
  let ipat = Option.map (fun (b, ipat) -> (b, CAst.make @@ mk_intro_pattern_naming ipat)) ipat in
  let cl = mk_clause cl in
  Tactics.letin_pat_tac ev ipat na c cl

(** Ltac interface treats differently global references than other term
    arguments in reduction expressions. In Ltac1, this is done at parsing time.
    Instead, we parse indifferently any pattern and dispatch when the tactic is
    called. *)
let map_pattern_with_occs (pat, occ) = match pat with
| Pattern.PRef (ConstRef cst) -> (mk_occurrences_expr occ, Inl (EvalConstRef cst))
| Pattern.PRef (VarRef id) -> (mk_occurrences_expr occ, Inl (EvalVarRef id))
| _ -> (mk_occurrences_expr occ, Inr pat)

let get_evaluable_reference = function
| VarRef id -> Proofview.tclUNIT (EvalVarRef id)
| ConstRef cst -> Proofview.tclUNIT (EvalConstRef cst)
| r ->
  Tacticals.New.tclZEROMSG (str "Cannot coerce" ++ spc () ++
    Nametab.pr_global_env Id.Set.empty r ++ spc () ++
    str "to an evaluable reference.")

let reduce r cl =
  let cl = mk_clause cl in
  Tactics.reduce r cl

let simpl flags where cl =
  let where = Option.map map_pattern_with_occs where in
  let cl = mk_clause cl in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Simpl (flags, where)) cl

let cbv flags cl =
  let cl = mk_clause cl in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Cbv flags) cl

let cbn flags cl =
  let cl = mk_clause cl in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Cbn flags) cl

let lazy_ flags cl =
  let cl = mk_clause cl in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Lazy flags) cl

let unfold occs cl =
  let cl = mk_clause cl in
  let map (gr, occ) =
    let occ = mk_occurrences_expr occ in
    get_evaluable_reference gr >>= fun gr -> Proofview.tclUNIT (occ, gr)
  in
  Proofview.Monad.List.map map occs >>= fun occs ->
  Tactics.reduce (Unfold occs) cl

let pattern where cl =
  let where = List.map (fun (c, occ) -> (mk_occurrences_expr occ, c)) where in
  let cl = mk_clause cl in
  Tactics.reduce (Pattern where) cl

let vm where cl =
  let where = Option.map map_pattern_with_occs where in
  let cl = mk_clause cl in
  Tactics.reduce (CbvVm where) cl

let native where cl =
  let where = Option.map map_pattern_with_occs where in
  let cl = mk_clause cl in
  Tactics.reduce (CbvNative where) cl

let eval_fun red c =
  Tac2core.pf_apply begin fun env sigma ->
  let (redfun, _) = Redexpr.reduction_of_red_expr env red in
  let (sigma, ans) = redfun env sigma c in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  Proofview.tclUNIT ans
  end

let eval_red c =
  eval_fun (Red false) c

let eval_hnf c =
  eval_fun Hnf c

let eval_simpl flags where c =
  let where = Option.map map_pattern_with_occs where in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun (Simpl (flags, where)) c

let eval_cbv flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun (Cbv flags) c

let eval_cbn flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun (Cbn flags) c

let eval_lazy flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun (Lazy flags) c

let eval_unfold occs c =
  let map (gr, occ) =
    let occ = mk_occurrences_expr occ in
    get_evaluable_reference gr >>= fun gr -> Proofview.tclUNIT (occ, gr)
  in
  Proofview.Monad.List.map map occs >>= fun occs ->
  eval_fun (Unfold occs) c

let eval_fold cl c =
  eval_fun (Fold cl) c

let eval_pattern where c =
  let where = List.map (fun (pat, occ) -> (mk_occurrences_expr occ, pat)) where in
  eval_fun (Pattern where) c

let eval_vm where c =
  let where = Option.map map_pattern_with_occs where in
  eval_fun (CbvVm where) c

let eval_native where c =
  let where = Option.map map_pattern_with_occs where in
  eval_fun (CbvNative where) c

let on_destruction_arg tac ev arg =
  Proofview.Goal.enter begin fun gl ->
  match arg with
  | None -> tac ev None
  | Some (clear, arg) ->
    let arg = match arg with
    | ElimOnConstr c ->
      let env = Proofview.Goal.env gl in
      Proofview.tclEVARMAP >>= fun sigma ->
      c >>= fun (c, lbind) ->
      let lbind = mk_bindings lbind in
      Proofview.tclEVARMAP >>= fun sigma' ->
      let flags = tactic_infer_flags ev in
      let (sigma', c) = Unification.finish_evar_resolution ~flags env sigma' (sigma, c) in
      Proofview.tclUNIT (Some sigma', Tactics.ElimOnConstr (c, lbind))
    | ElimOnIdent id -> Proofview.tclUNIT (None, Tactics.ElimOnIdent CAst.(make id))
    | ElimOnAnonHyp n -> Proofview.tclUNIT (None, Tactics.ElimOnAnonHyp n)
    in
    arg >>= fun (sigma', arg) ->
    let arg = Some (clear, arg) in
    match sigma' with
    | None -> tac ev arg
    | Some sigma' ->
      Tacticals.New.tclWITHHOLES ev (tac ev arg) sigma'
  end

let discriminate ev arg =
  let arg = Option.map (fun arg -> None, arg) arg in
  on_destruction_arg Equality.discr_tac ev arg

let injection ev ipat arg =
  let arg = Option.map (fun arg -> None, arg) arg in
  let ipat = Option.map mk_intro_patterns ipat in
  let tac ev arg = Equality.injClause None ipat ev arg in
  on_destruction_arg tac ev arg

let autorewrite ~all by ids cl =
  let conds = if all then Some Equality.AllMatches else None in
  let ids = List.map Id.to_string ids in
  let cl = mk_clause cl in
  match by with
  | None -> Autorewrite.auto_multi_rewrite ?conds ids cl
  | Some by ->
    let by = thaw Tac2ffi.unit by in
    Autorewrite.auto_multi_rewrite_with ?conds by ids cl

(** Auto *)

let trivial debug lems dbs =
  let lems = List.map (fun c -> delayed_of_thunk Tac2ffi.constr c) lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.h_trivial ~debug lems dbs

let auto debug n lems dbs =
  let lems = List.map (fun c -> delayed_of_thunk Tac2ffi.constr c) lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.h_auto ~debug n lems dbs

let new_auto debug n lems dbs =
  let make_depth n = snd (Eauto.make_dimension n None) in
  let lems = List.map (fun c -> delayed_of_thunk Tac2ffi.constr c) lems in
  match dbs with
  | None -> Auto.new_full_auto ~debug (make_depth n) lems
  | Some dbs ->
    let dbs = List.map Id.to_string dbs in
    Auto.new_auto ~debug (make_depth n) lems dbs

let eauto debug n p lems dbs =
  let lems = List.map (fun c -> delayed_of_thunk Tac2ffi.constr c) lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Eauto.gen_eauto (Eauto.make_dimension n p) lems dbs

let typeclasses_eauto strategy depth dbs =
  let only_classes, dbs = match dbs with
  | None ->
    true, [Class_tactics.typeclasses_db]
  | Some dbs ->
    let dbs = List.map Id.to_string dbs in
    false, dbs
  in
  Class_tactics.typeclasses_eauto ~only_classes ?strategy ~depth dbs

(** Inversion *)

let inversion knd arg pat ids =
  let ids = match ids with
  | None -> []
  | Some l -> l
  in
  begin match pat with
  | None -> Proofview.tclUNIT None
  | Some (IntroAction (IntroOrAndPattern p)) ->
    Proofview.tclUNIT (Some (CAst.make @@ mk_or_and_intro_pattern p))
  | Some _ ->
    Tacticals.New.tclZEROMSG (str "Inversion only accept disjunctive patterns")
  end >>= fun pat ->
  let inversion _ arg =
    begin match arg with
    | None -> assert false
    | Some (_, Tactics.ElimOnAnonHyp n) ->
      Inv.inv_clause knd pat ids (AnonHyp n)
    | Some (_, Tactics.ElimOnIdent {CAst.v=id}) ->
      Inv.inv_clause knd pat ids (NamedHyp id)
    | Some (_, Tactics.ElimOnConstr c) ->
      let open Tactypes in
      let anon = CAst.make @@ IntroNaming Namegen.IntroAnonymous in
      Tactics.specialize c (Some anon) >>= fun () ->
      Tacticals.New.onLastHypId (fun id -> Inv.inv_clause knd pat ids (NamedHyp id))
    end
  in
  on_destruction_arg inversion true (Some (None, arg))

let contradiction c =
  let c = Option.map mk_with_bindings c in
  Contradiction.contradiction c
