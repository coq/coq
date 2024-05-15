(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Proofview.Notations

let generic_refine ~typecheck f gl =
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let state = Proofview.Goal.state gl in
  (* Save the [future_goals] state to restore them after the
     refinement. *)
  let sigma = Evd.push_future_goals sigma in
  (* Create the refinement term *)
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  f >>= fun (v, c, principal) ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.wrap_exceptions begin fun () ->
  (* Redo the effects in sigma in the monad's env *)
  let privates_csts = Evd.eval_side_effects sigma in
  let env = Safe_typing.push_private_constants env privates_csts.Evd.seff_private in
  (* Check that the refined term is typesafe *)
  let sigma = if typecheck then Typing.check env sigma c concl else sigma in
  (* Check that the goal itself does not appear in the refined term *)
  let self = Proofview.Goal.goal gl in
  let _ =
    if not (Evarutil.occur_evar_upto sigma self c) then ()
    else Pretype_errors.error_occur_check env sigma self c
  in
  (* Restore the [future goals] state. *)
  let future_goals, sigma = Evd.pop_future_goals sigma in
  (* Select the goals *)
  let future_goals = Evd.FutureGoals.map_filter (Proofview.Unsafe.advance sigma) future_goals in
  let shelf = Evd.shelf sigma in
  let future_goals = Evd.FutureGoals.filter (fun ev -> not @@ List.mem ev shelf) future_goals in
  (* Proceed to the refinement *)
  let sigma = match Proofview.Unsafe.advance sigma self with
  | None ->
    (* Nothing to do, the goal has been solved by side-effect *)
    sigma
  | Some self ->
    match principal with
    | None -> Evd.define self c sigma
    | Some evk ->
        let id = Evd.evar_ident self sigma in
        let sigma = Evd.define self c sigma in
        match id with
        | None -> sigma
        | Some id -> Evd.rename evk id sigma
  in
  (* Mark goals *)
  let sigma = Proofview.Unsafe.mark_as_goals sigma (Evd.FutureGoals.comb future_goals) in
  let comb = CList.rev_map (fun x -> Proofview.goal_with_state x state) (Evd.FutureGoals.comb future_goals) in
  let trace () = Pp.(hov 2 (str"simple refine"++spc()++
                                   Termops.Internal.print_constr_env env sigma c)) in
  Proofview.Trace.name_tactic trace (Proofview.tclUNIT v) >>= fun v ->
  Proofview.Unsafe.tclSETENV (Environ.reset_context env) <*>
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS comb <*>
  Proofview.tclUNIT v
  end

let lift c =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.wrap_exceptions begin fun () ->
  let (sigma, c) = c sigma in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  Proofview.tclUNIT c
  end

let make_refine_enter ~typecheck f gl = generic_refine ~typecheck (lift f) gl

let refine ~typecheck f =
  let f evd =
    let (evd,c) = f evd in (evd,((), c, None))
  in
  Proofview.Goal.enter (make_refine_enter ~typecheck f)

let refine_with_principal ~typecheck f =
  let f evd =
    let (evd,c, principal) = f evd in (evd,((), c, principal))
  in
  Proofview.Goal.enter (make_refine_enter ~typecheck f)

(** {7 solve_constraints}

  Ensure no remaining unification problems are left. Run at every "." by default. *)

let solve_constraints =
  let open Proofview in
  tclENV >>= fun env -> tclEVARMAP >>= fun sigma ->
   try let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
       Unsafe.tclEVARSADVANCE sigma
   with e when CErrors.noncritical e ->
     let e, info = Exninfo.capture e in
     tclZERO ~info e
