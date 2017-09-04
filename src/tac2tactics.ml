(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Globnames
open Misctypes
open Tactypes
open Genredexpr
open Proofview
open Proofview.Notations

type destruction_arg = EConstr.constr with_bindings tactic Misctypes.destruction_arg

let tactic_infer_flags with_evar = {
  Pretyping.use_typeclasses = true;
  Pretyping.solve_unification_constraints = true;
  Pretyping.use_hook = None;
  Pretyping.fail_evar = not with_evar;
  Pretyping.expand_evars = true }

(** FIXME: export a better interface in Tactics *)
let delayed_of_tactic tac env sigma =
  let _, pv = Proofview.init sigma [] in
  let c, pv, _, _ = Proofview.apply env tac pv in
  (sigma, c)

let apply adv ev cb cl =
  let map c = None, Loc.tag (delayed_of_tactic c) in
  let cb = List.map map cb in
  match cl with
  | None -> Tactics.apply_with_delayed_bindings_gen adv ev cb
  | Some (id, cl) -> Tactics.apply_delayed_in adv ev id cb cl

type induction_clause =
  destruction_arg *
  intro_pattern_naming option *
  or_and_intro_pattern option *
  Locus.clause option

let map_destruction_arg = function
| ElimOnConstr c -> ElimOnConstr (delayed_of_tactic c)
| ElimOnIdent id -> ElimOnIdent id
| ElimOnAnonHyp n -> ElimOnAnonHyp n

let map_induction_clause ((clear, arg), eqn, as_, occ) =
  ((clear, map_destruction_arg arg), (eqn, as_), occ)

let induction_destruct isrec ev ic using =
  let ic = List.map map_induction_clause ic in
  Tactics.induction_destruct isrec ev (ic, using)

type rewriting =
  bool option *
  multi *
  EConstr.constr with_bindings tactic

let rewrite ev rw cl by =
  let map_rw (orient, repeat, c) =
    (Option.default true orient, repeat, None, delayed_of_tactic c)
  in
  let rw = List.map map_rw rw in
  let by = Option.map (fun tac -> Tacticals.New.tclCOMPLETE tac, Equality.Naive) by in
  Equality.general_multi_rewrite ev rw cl by

(** Ltac interface treats differently global references than other term
    arguments in reduction expressions. In Ltac1, this is done at parsing time.
    Instead, we parse indifferently any pattern and dispatch when the tactic is
    called. *)
let map_pattern_with_occs (pat, occ) = match pat with
| Pattern.PRef (ConstRef cst) -> (occ, Inl (EvalConstRef cst))
| Pattern.PRef (VarRef id) -> (occ, Inl (EvalVarRef id))
| _ -> (occ, Inr pat)

let get_evaluable_reference = function
| VarRef id -> Proofview.tclUNIT (EvalVarRef id)
| ConstRef cst -> Proofview.tclUNIT (EvalConstRef cst)
| r ->
  Tacticals.New.tclZEROMSG (str "Cannot coerce" ++ spc () ++
    Nametab.pr_global_env Id.Set.empty r ++ spc () ++
    str "to an evaluable reference.")

let simpl flags where cl =
  let where = Option.map map_pattern_with_occs where in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Simpl (flags, where)) cl

let cbv flags cl =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Cbv flags) cl

let cbn flags cl =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Cbn flags) cl

let lazy_ flags cl =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  Tactics.reduce (Lazy flags) cl

let unfold occs cl =
  let map (gr, occ) =
    get_evaluable_reference gr >>= fun gr -> Proofview.tclUNIT (occ, gr)
  in
  Proofview.Monad.List.map map occs >>= fun occs ->
  Tactics.reduce (Unfold occs) cl

let vm where cl =
  let where = Option.map map_pattern_with_occs where in
  Tactics.reduce (CbvVm where) cl

let native where cl =
  let where = Option.map map_pattern_with_occs where in
  Tactics.reduce (CbvNative where) cl

let eval_fun bt red c =
  Tac2core.pf_apply bt begin fun env sigma ->
  let (redfun, _) = Redexpr.reduction_of_red_expr env red in
  let (sigma, ans) = redfun env sigma c in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  Proofview.tclUNIT ans
  end

let eval_red bt c =
  eval_fun bt (Red false) c

let eval_hnf bt c =
  eval_fun bt Hnf c

let eval_simpl bt flags where c =
  let where = Option.map map_pattern_with_occs where in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun bt (Simpl (flags, where)) c

let eval_cbv bt flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun bt (Cbv flags) c

let eval_cbn bt flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun bt (Cbn flags) c

let eval_lazy bt flags c =
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let flags = { flags with rConst } in
  eval_fun bt (Lazy flags) c

let eval_unfold bt occs c =
  let map (gr, occ) =
    get_evaluable_reference gr >>= fun gr -> Proofview.tclUNIT (occ, gr)
  in
  Proofview.Monad.List.map map occs >>= fun occs ->
  eval_fun bt (Unfold occs) c

let eval_fold bt cl c =
  eval_fun bt (Fold cl) c

let eval_pattern bt where c =
  let where = List.map (fun (pat, occ) -> (occ, pat)) where in
  eval_fun bt (Pattern where) c

let eval_vm bt where c =
  let where = Option.map map_pattern_with_occs where in
  eval_fun bt (CbvVm where) c

let eval_native bt where c =
  let where = Option.map map_pattern_with_occs where in
  eval_fun bt (CbvNative where) c

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
      Proofview.tclEVARMAP >>= fun sigma' ->
      let flags = tactic_infer_flags ev in
      let (sigma', c) = Unification.finish_evar_resolution ~flags env sigma' (sigma, c) in
      Proofview.tclUNIT (Some sigma', ElimOnConstr (c, lbind))
    | ElimOnIdent id -> Proofview.tclUNIT (None, ElimOnIdent id)
    | ElimOnAnonHyp n -> Proofview.tclUNIT (None, ElimOnAnonHyp n)
    in
    arg >>= fun (sigma', arg) ->
    let arg = Some (clear, arg) in
    match sigma' with
    | None -> tac ev arg
    | Some sigma' ->
      Tacticals.New.tclWITHHOLES ev (tac ev arg) sigma'
  end

let discriminate ev arg = on_destruction_arg Equality.discr_tac ev arg

let injection ev ipat arg =
  let tac ev arg = Equality.injClause ipat ev arg in
  on_destruction_arg tac ev arg

let autorewrite ~all by ids cl =
  let conds = if all then Some Equality.AllMatches else None in
  let ids = List.map Id.to_string ids in
  match by with
  | None -> Autorewrite.auto_multi_rewrite ?conds ids cl
  | Some by -> Autorewrite.auto_multi_rewrite_with ?conds by ids cl

(** Auto *)

let trivial debug lems dbs =
  let lems = List.map delayed_of_tactic lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.h_trivial ~debug lems dbs

let auto debug n lems dbs =
  let lems = List.map delayed_of_tactic lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Auto.h_auto ~debug n lems dbs

let new_auto debug n lems dbs =
  let make_depth n = snd (Eauto.make_dimension n None) in
  let lems = List.map delayed_of_tactic lems in
  match dbs with
  | None -> Auto.new_full_auto ~debug (make_depth n) lems
  | Some dbs ->
    let dbs = List.map Id.to_string dbs in
    Auto.new_auto ~debug (make_depth n) lems dbs

let eauto debug n p lems dbs =
  let lems = List.map delayed_of_tactic lems in
  let dbs = Option.map (fun l -> List.map Id.to_string l) dbs in
  Eauto.gen_eauto (Eauto.make_dimension n p) lems dbs

let typeclasses_eauto strategy depth dbs =
  let only_classes, dbs = match dbs with
  | None ->
    true, [Hints.typeclasses_db]
  | Some dbs ->
    let dbs = List.map Id.to_string dbs in
    false, dbs
  in
  Class_tactics.typeclasses_eauto ~only_classes ~strategy ~depth dbs
