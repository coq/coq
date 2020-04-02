(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Evd

let use_unification_heuristics =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Solve";"Unification";"Constraints"]
    ~value:true

let solve ?with_end_tac gi info_lvl tac pr =
    let tac = match with_end_tac with
      | None -> tac
      | Some etac -> Proofview.tclTHEN tac etac in
    let tac = match info_lvl with
      | None -> tac
      | Some _ -> Proofview.Trace.record_info_trace tac
    in
    let nosuchgoal = Proofview.tclZERO (Proof_bullet.SuggestNoSuchGoals (1,pr)) in
    let tac = let open Goal_select in match gi with
      | SelectAlreadyFocused ->
        let open Proofview.Notations in
        Proofview.numgoals >>= fun n ->
        if n == 1 then tac
        else
          let e = CErrors.UserError
              (None,
               Pp.(str "Expected a single focused goal but " ++
                   int n ++ str " goals are focused."))
          in
          Proofview.tclZERO e

      | SelectNth i -> Proofview.tclFOCUS ~nosuchgoal i i tac
      | SelectList l -> Proofview.tclFOCUSLIST ~nosuchgoal l tac
      | SelectId id -> Proofview.tclFOCUSID ~nosuchgoal id tac
      | SelectAll -> tac
    in
    let tac =
      if use_unification_heuristics () then
        Proofview.tclTHEN tac Refine.solve_constraints
      else tac
    in
    let env = Global.env () in
    let (p,(status,info),()) = Proof.run_tactic env tac pr in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let () =
      match info_lvl with
      | None -> ()
      | Some i -> Feedback.msg_info (hov 0 (Proofview.Trace.pr_info env sigma ~lvl:i info))
    in
    (p,status)

(**********************************************************************)
(* Shortcut to build a term using tactics *)

let refine_by_tactic ~name ~poly env sigma ty tac =
  (* Save the initial side-effects to restore them afterwards. We set the
     current set of side-effects to be empty so that we can retrieve the
     ones created during the tactic invocation easily. *)
  let eff = Evd.eval_side_effects sigma in
  let sigma = Evd.drop_side_effects sigma in
  (* Save the existing goals *)
  let prev_future_goals = save_future_goals sigma in
  (* Start a proof *)
  let prf = Proof.start ~name ~poly sigma [env, ty] in
  let (prf, _, ()) =
    try Proof.run_tactic env tac prf
    with Logic_monad.TacticFailure e as src ->
      (* Catch the inner error of the monad tactic *)
      let (_, info) = Exninfo.capture src in
      Exninfo.iraise (e, info)
  in
  (* Plug back the retrieved sigma *)
  let Proof.{ goals; stack; shelf; given_up; sigma; entry } = Proof.data prf in
  assert (stack = []);
  let ans = match Proofview.initial_goals entry with
  | [c, _] -> c
  | _ -> assert false
  in
  let ans = EConstr.to_constr ~abort_on_undefined_evars:false sigma ans in
  (* [neff] contains the freshly generated side-effects *)
  let neff = Evd.eval_side_effects sigma in
  (* Reset the old side-effects *)
  let sigma = Evd.drop_side_effects sigma in
  let sigma = Evd.emit_side_effects eff sigma in
  (* Restore former goals *)
  let sigma = restore_future_goals sigma prev_future_goals in
  (* Push remaining goals as future_goals which is the only way we
     have to inform the caller that there are goals to collect while
     not being encapsulated in the monad *)
  (* Goals produced by tactic "shelve" *)
  let sigma = List.fold_right (Evd.declare_future_goal ~tag:Evd.ToShelve) shelf sigma in
  (* Goals produced by tactic "give_up" *)
  let sigma = List.fold_right (Evd.declare_future_goal ~tag:Evd.ToGiveUp) given_up sigma in
  (* Other goals *)
  let sigma = List.fold_right Evd.declare_future_goal goals sigma in
  (* Get rid of the fresh side-effects by internalizing them in the term
     itself. Note that this is unsound, because the tactic may have solved
     other goals that were already present during its invocation, so that
     those goals rely on effects that are not present anymore. Hopefully,
     this hack will work in most cases. *)
  let neff = neff.Evd.seff_private in
  let (ans, _) = Safe_typing.inline_private_constants env ((ans, Univ.ContextSet.empty), neff) in
  ans, sigma
