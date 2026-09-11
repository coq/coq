(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Tac2types
open Genredexpr
open Proofview.Notations

let return = Proofview.tclUNIT
let thaw (f:unit -> _ Proofview.tactic) = f ()

let tactic_infer_flags with_evar = Pretyping.{
  use_coercions = true;
  use_typeclasses = UseTC;
  solve_unification_constraints = true;
  fail_evar = not with_evar;
  expand_evars = true;
  program_mode = false;
  poly = PolyFlags.default;
  undeclared_evars_rr = false;
  unconstrained_sorts = false;
}

(** FIXME: export a better interface in Tactics *)
let delayed_of_tactic tac env sigma =
  let _, pv = Proofview.init sigma [] in
  let name, poly = Id.of_string "ltac2_delayed", PolyFlags.default in
  let c, pv, _, _, _ = Proofview.apply ~name ~poly env tac pv in
  let _, sigma = Proofview.proofview pv in
  (sigma, c)

let delayed_of_thunk r tac env sigma =
  delayed_of_tactic (thaw tac) env sigma

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

let mk_occurrences = function
| AllOccurrences -> Locus.AllOccurrences
| AllOccurrencesBut l -> Locus.AllOccurrencesBut l
| NoOccurrences -> Locus.NoOccurrences
| OnlyOccurrences l -> Locus.OnlyOccurrences l

let mk_occurrences_expr occs =
  let occs = mk_occurrences occs in
  Locusops.occurrences_map (List.map (fun i -> Locus.ArgArg i)) occs

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
    let c = thaw c >>= fun p -> return (mk_with_bindings p) in
    None, CAst.make c
  in
  let cb = List.map map cb in
  match cl with
  | None -> Tactics.apply_with_delayed_bindings_gen adv ev cb
  | Some (id, cl) ->
    let cl = Option.map mk_intro_pattern cl in
    Tactics.apply_delayed_in adv ev id cb cl Tacticals.tclIDTAC

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
  Induction.induction_destruct isrec ev (ic, using)

let elim ev c copt =
  let c = mk_with_bindings c in
  let copt = Option.map mk_with_bindings copt in
  Tactics.elim ev None c copt

let generalize pl =
  let mk_occ occs = mk_occurrences occs in
  let pl = List.map (fun (c, occs, na) -> (mk_occ occs, c), na) pl in
  Generalize.new_generalize_gen pl

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
  Proofview.Goal.enter begin fun gl ->
  let c subst env sigma =
    let subst = Array.map_of_list snd (Id.Map.bindings subst) in
    Tacred.Changed (delayed_of_tactic (c subst) env sigma)
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
  let by = Option.map (fun tac -> Tacticals.tclCOMPLETE (thaw tac), Equality.Naive) by in
  Equality.general_multi_rewrite ev rw cl by

let setoid_rewrite orient c occs id =
  let c = c >>= fun c -> return (mk_with_bindings c) in
  let occs = mk_occurrences occs in
  Rewrite.cl_rewrite_clause (delayed_of_tactic c) orient occs id

let rewrite_strat strat clause =
  Rewrite.cl_rewrite_clause_strat strat clause

module RewriteStrats =
struct
  let fix f =
    let f s = Proofview.Monad.map Tac2ffi.to_rewstrategy (Tac2val.apply f [Tac2ffi.of_rewstrategy s]) in
    Rewrite.Strategies.fix_tac f

  let hints i =
    Rewrite.Strategies.hints (Id.to_string i)

  let old_hints i =
    Rewrite.Strategies.old_hints (Id.to_string i)

  let one_lemma c l2r =
    let c env sigma = Pretyping.understand_uconstr env sigma c in
    Rewrite.Strategies.one_lemma c l2r None AllOccurrences

  let lemmas cs =
    let mk_c c = (); fun env sigma -> Pretyping.understand_uconstr env sigma c in
    let mk_c c = (mk_c c, true, None) in
    let cs = List.map mk_c cs in
    Rewrite.Strategies.lemmas cs
end

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
  let tac = Option.map (fun tac -> thaw tac) tac in
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
| Pattern.PRef (GlobRef.ConstRef cst) -> (mk_occurrences occ, Inl (Evaluable.EvalConstRef cst))
| Pattern.PRef (GlobRef.VarRef id) -> (mk_occurrences occ, Inl (Evaluable.EvalVarRef id))
| _ -> (mk_occurrences occ, Inr pat)

let get_evaluable_reference = function
| GlobRef.VarRef id -> Proofview.tclUNIT (Evaluable.EvalVarRef id)
| GlobRef.ConstRef cst -> Proofview.tclUNIT (Evaluable.EvalConstRef cst)
| r -> Proofview.tclZERO (Tacred.NotEvaluableRef r)

let mk_flags flags =
  Proofview.Monad.map
    (fun rConst -> { flags with rConst })
    (Proofview.Monad.List.map get_evaluable_reference flags.rConst)

let reduce_in red cl =
  let cl = mk_clause cl in
  Tactics.reduce red cl

let reduce_constr env sigma red c =
  let (redfun, _) = Redexpr.reduction_of_red_expr env red in
  let (sigma, ans) = redfun env sigma c in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  Proofview.tclUNIT ans

let simpl flags where =
  Proofview.Monad.map
    (fun flags ->
       let where = Option.map map_pattern_with_occs where in
       (Simpl (flags, where)))
    (mk_flags flags)

let cbv flags =
  Proofview.Monad.map
    (fun flags -> Cbv flags)
    (mk_flags flags)

let cbn flags  =
  Proofview.Monad.map
    (fun flags -> Cbn flags)
    (mk_flags flags)

let lazy_ flags =
  Proofview.Monad.map
    (fun flags -> Lazy flags)
    (mk_flags flags)

let unfold occs =
  let map (gr, occ) =
    let occ = mk_occurrences occ in
    get_evaluable_reference gr >>= fun gr -> Proofview.tclUNIT (occ, gr)
  in
  Proofview.Monad.map
    (fun occs -> Unfold occs)
    (Proofview.Monad.List.map map occs)

let pattern where =
  let where = List.map (fun (c, occ) -> (mk_occurrences occ, c)) where in
  Pattern where

let vm where =
  let where = Option.map map_pattern_with_occs where in
  CbvVm where

let native where =
  let where = Option.map map_pattern_with_occs where in
  CbvNative where

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
      let (sigma', c) = Tactics.finish_evar_resolution ~flags env sigma' (Some sigma, c) in
      Proofview.tclUNIT (Some sigma', Tactics.ElimOnConstr (c, lbind))
    | ElimOnIdent id -> Proofview.tclUNIT (None, Tactics.ElimOnIdent CAst.(make id))
    | ElimOnAnonHyp n -> Proofview.tclUNIT (None, Tactics.ElimOnAnonHyp n)
    in
    arg >>= fun (sigma', arg) ->
    let arg = Some (clear, arg) in
    match sigma' with
    | None -> tac ev arg
    | Some sigma' ->
      Tacticals.tclWITHHOLES ev (tac ev arg) sigma'
  end

let discriminate ev arg =
  let arg = Option.map (fun arg -> None, arg) arg in
  on_destruction_arg Equality.discr_tac ev arg

let injection ev ipat arg =
  let arg = Option.map (fun arg -> None, arg) arg in
  let ipat = Option.map mk_intro_patterns ipat in
  let tac ev arg = Equality.injClause None ipat ev arg in
  on_destruction_arg tac ev arg

let autorewrite ~all ?(forward=true) by ids cl =
  let conds = if all then Some Equality.AllMatches else None in
  let ids = List.map Id.to_string ids in
  let cl = mk_clause cl in
  match by with
  | None -> Autorewrite.auto_multi_rewrite ?conds ~forward ids cl
  | Some by ->
    let by = thaw by in
    Autorewrite.auto_multi_rewrite_with ?conds ~forward by ids cl

(** Auto *)

let delayed_of_globref gr = (); fun env sigma ->
  Evd.fresh_global env sigma gr

let trivial debug lems dbs =
  let lems = List.map delayed_of_globref lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.gen_trivial ~debug lems dbs

let auto debug n lems dbs =
  let lems = List.map delayed_of_globref lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.gen_auto ~debug n lems dbs

let eauto debug n lems dbs =
  let lems = List.map delayed_of_globref lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Eauto.gen_eauto ~debug ?depth:n lems dbs

let typeclasses_eauto strategy depth dbs =
  let only_classes, dbs = match dbs with
  | None ->
    true, [Class_tactics.typeclasses_db]
  | Some dbs ->
    let dbs = List.map Id.to_string dbs in
    false, dbs
  in
  Class_tactics.typeclasses_eauto ~only_classes ?strategy ~depth dbs

let unify x y = Tactics.unify x y

let current_transparent_state () =
  Proofview.tclENV >>= fun env ->
  let state = Conv_oracle.get_transp_state (Environ.oracle env) in
  Proofview.tclUNIT state

let with_strategy lvl ql tac =
  Tactics.with_set_strategy [(lvl, ql)] (thaw tac)

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
    Tacticals.tclZEROMSG (str "Inversion only accept disjunctive patterns")
  end >>= fun pat ->
  let inversion _ arg =
    begin match arg with
    | None -> assert false
    | Some (_, Tactics.ElimOnAnonHyp n) ->
      Inv.inv_clause knd pat ids (AnonHyp n)
    | Some (_, Tactics.ElimOnIdent id) ->
      Inv.inv_clause knd pat ids (NamedHyp id)
    | Some (_, Tactics.ElimOnConstr c) ->
      let open Tactypes in
      let anon = CAst.make @@ IntroNaming Namegen.IntroAnonymous in
      Tactics.specialize c (Some anon) >>= fun () ->
      Tacticals.onLastHypId (fun id -> Inv.inv_clause knd pat ids (NamedHyp (CAst.make id)))
    end
  in
  on_destruction_arg inversion true (Some (None, arg))

let contradiction c =
  let c = Option.map mk_with_bindings c in
  Contradiction.contradiction c

let congruence n l = Cc_core_plugin.Cctac.congruence_tac n (Option.default [] l)

let simple_congruence n l = Cc_core_plugin.Cctac.simple_congruence_tac n (Option.default [] l)

let f_equal = Cc_core_plugin.Cctac.f_equal

(* Strategy tactic call *)

let wrap_tactic_call f =
  let open Evarutil in
  let open Proofview in
  let open Proofview.Notations in
  let wrapf ~env ~carrier ~lhs ~rel =
    Proofview.tclEVARMAP >>= fun sigma ->
      let ectx = ext_named_context_of_env env sigma in
      let subst = ext_csubst ectx in
      let carriern = Evarutil.csubst_subst sigma subst carrier in
      let lhsn = Evarutil.csubst_subst sigma subst lhs in
      let reln = Option.map (Evarutil.csubst_subst sigma subst) rel in
      let sigma, unit = Evd.fresh_global env sigma (Rocqlib.lib_ref "core.unit.type") in
      let sigma, unitval = Evd.fresh_global env sigma (Rocqlib.lib_ref "core.unit.tt") in
      let sigma, goalev = Evd.new_pure_evar ~relevance:EConstr.ERelevance.relevant (ext_named_context_val ectx) sigma unit in
      Unsafe.tclEVARS sigma <*>
      Unsafe.tclNEWGOALS [with_empty_state goalev] <*>
      f carriern lhsn reln >>= fun res ->
      tclEVARMAP >>= fun sigma ->
      if Evd.is_defined sigma goalev then
        Tacticals.tclZEROMSG Pp.(str"The tactic called by Ltac2.Rewrite.Strategy.tactic should not solve the goal, it is provided as read-only information.")
      else
        let rev_subst = ext_rev_subst ectx in
        let res = Rewrite.Result.subst sigma rev_subst res in
        Unsafe.tclEVARS (Evd.define goalev unitval sigma) <*> tclUNIT res
  in Rewrite.Strategies.tactic_call wrapf
