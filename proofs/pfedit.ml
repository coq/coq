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
open Environ
open Evd

let use_unification_heuristics_ref = ref true
let () = Goptions.(declare_bool_option {
  optdepr = false;
  optname = "Solve unification constraints at every \".\"";
  optkey = ["Solve";"Unification";"Constraints"];
  optread = (fun () -> !use_unification_heuristics_ref);
  optwrite = (fun a -> use_unification_heuristics_ref:=a);
})

let use_unification_heuristics () = !use_unification_heuristics_ref

exception NoSuchGoal
let () = CErrors.register_handler begin function
  | NoSuchGoal -> CErrors.user_err Pp.(str "No such goal.")
  | _ -> raise CErrors.Unhandled
end

let get_nth_V82_goal p i =
  let Proof.{ sigma; goals } = Proof.data p in
  try { it = List.nth goals (i-1) ; sigma }
  with Failure _ -> raise NoSuchGoal

let get_goal_context_gen pf i =
  let { it=goal ; sigma=sigma; } = get_nth_V82_goal pf i in
  (sigma, Refiner.pf_env { it=goal ; sigma=sigma; })

let get_goal_context pf i =
  let p = Proof_global.get_proof pf in
  get_goal_context_gen p i

let get_current_goal_context pf =
  let p = Proof_global.get_proof pf in
  try get_goal_context_gen p 1
  with
  | NoSuchGoal ->
    (* spiwack: returning empty evar_map, since if there is no goal,
       under focus, there is no accessible evar either. EJGA: this
       seems strange, as we have pf *)
    let env = Global.env () in
    Evd.from_env env, env

let get_current_context pf =
  let p = Proof_global.get_proof pf in
  try get_goal_context_gen p 1
  with
  | NoSuchGoal ->
    (* No more focused goals *)
    let evd = Proof.in_proof p (fun x -> x) in
    evd, Global.env ()

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

let by tac = Proof_global.map_fold_proof (solve (Goal_select.SelectNth 1) None tac)

(**********************************************************************)
(* Shortcut to build a term using tactics *)

let next = let n = ref 0 in fun () -> incr n; !n

let build_constant_by_tactic ~name ctx sign ~poly typ tac =
  let evd = Evd.from_ctx ctx in
  let goals = [ (Global.env_of_context sign , typ) ] in
  let pf = Proof_global.start_proof ~name ~poly ~udecl:UState.default_univ_decl evd goals in
  try
    let pf, status = by tac pf in
    let open Proof_global in
    let { entries; universes } = close_proof ~opaque:Transparent ~keep_body_ucst_separate:false (fun x -> x) pf in
    match entries with
    | [entry] ->
      let univs = UState.demote_seff_univs entry.Proof_global.proof_entry_universes universes in
      entry, status, univs
    | _ ->
      CErrors.anomaly Pp.(str "[build_constant_by_tactic] close_proof returned more than one proof term")
  with reraise ->
    let reraise = CErrors.push reraise in
    iraise reraise

let build_by_tactic ?(side_eff=true) env sigma ~poly typ tac =
  let name = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = val_of_named_context (named_context env) in
  let ce, status, univs = build_constant_by_tactic ~name sigma sign ~poly typ tac in
  let body, eff = Future.force ce.Proof_global.proof_entry_body in
  let (cb, ctx) =
    if side_eff then Safe_typing.inline_private_constants env (body, eff.Evd.seff_private)
    else body
  in
  let univs = UState.merge ~sideff:side_eff ~extend:true Evd.univ_rigid univs ctx in
  cb, status, univs

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
      let (_, info) = CErrors.push src in
      iraise (e, info)
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
