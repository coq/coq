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

let stm_pr_err s  = Format.eprintf "%s] %s\n%!"     (Spawned.process_id ()) s

type 'a result = Val of 'a | Exn of exn

module TacTask : sig

  type output = (Constr.constr * UState.t) option
  type task = {
    t_state    : Vernacstate.t;
    t_assign   : output result option ref;
    t_ast      : ComTactic.interpretable;
    t_goalno   : int;
    t_goal     : Evar.t;
    t_kill     : unit -> unit;
    t_name     : string }

  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)

  let forward_feedback { Feedback.doc_id = did; span_id = id; route; contents } =
    Feedback.feedback ~did ~id ~route contents

  type output = (Constr.constr * UState.t) option

  type task = {
    t_state    : Vernacstate.t;
    t_assign   : output result option ref;
    t_ast      : ComTactic.interpretable;
    t_goalno   : int;
    t_goal     : Evar.t;
    t_kill     : unit -> unit;
    t_name     : string }

  type request = {
    r_state    : Vernacstate.t option;
    r_ast      : ComTactic.interpretable;
    r_goalno   : int;
    r_goal     : Evar.t;
    r_name     : string }

  type response =
    | RespBuiltSubProof of (Constr.constr * UState.t)
    | RespError of Pp.t
    | RespNoProgress

  let name = ref "tacticworker"
  let extra_env () = [||]
  type competence = unit
  type worker_status = Fresh | Old of competence

  let task_match _ _ = true

  (* run by the master, on a thread *)
  let request_of_task age { t_state; t_ast; t_goalno; t_goal; t_name } =
    Some {
      r_state    = if age <> Fresh then None else Some t_state;
      r_ast      = t_ast;
      r_goalno   = t_goalno;
      r_goal     = t_goal;
      r_name     = t_name }

  let assign r v =
    let () = assert (Option.is_empty !r) in
    r := Some v

  let use_response _ { t_assign; t_kill } resp =
    match resp with
    | RespBuiltSubProof o -> assign t_assign (Val (Some o)); `Stay ((),[])
    | RespNoProgress ->
        assign t_assign (Val None);
        t_kill ();
        `Stay ((),[])
    | RespError msg ->
        let e = (AsyncTaskQueue.RemoteException msg) in
        assign t_assign (Exn e);
        t_kill ();
        `Stay ((),[])

  let on_marshal_error err { t_name } =
    stm_pr_err ("Fatal marshal error: " ^ t_name );
    flush_all (); exit 1

  let on_task_cancellation_or_expiration_or_slave_death = function
    | Some { t_kill } -> t_kill ()
    | _ -> ()

  let command_focus = Proof.new_focus_kind ()
  let focus_cond = Proof.no_cond command_focus

  let state = ref None
  let receive_state = function
    | None -> ()
    | Some st -> state := Some st

  let perform { r_state = st; r_ast = tactic; r_goal; r_goalno } =
    receive_state st;
    Vernacstate.unfreeze_interp_state (Option.get !state);
    try
      Vernacstate.LemmaStack.with_top (Option.get (Option.get !state).Vernacstate.lemmas) ~f:(fun pstate ->
          let pstate =
            Declare.Proof.map pstate ~f:(Proof.focus focus_cond () r_goalno) in
          let pstate =
            ComTactic.solve ~pstate
              Goal_select.SelectAll ~info:None tactic ~with_end_tac:false in
          let { Proof.sigma } = Declare.Proof.fold pstate ~f:Proof.data in
          match Evd.(evar_body (find sigma r_goal)) with
          | Evd.Evar_empty -> RespNoProgress
          | Evd.Evar_defined t ->
              let t = Evarutil.nf_evar sigma t in
              let evars = Evarutil.undefined_evars_of_term sigma t in
              if Evar.Set.is_empty evars then
                let t = EConstr.Unsafe.to_constr t in
                RespBuiltSubProof (t, Evd.evar_universe_context sigma)
              else
                CErrors.user_err
                  Pp.(str"The par: selector requires a tactic that makes no progress or fully" ++
                      str" solves the goal and leaves no unresolved existential variables. The following" ++
                      str" existentials remain unsolved: " ++ prlist (Termops.pr_existential_key (Global.env ()) sigma) (Evar.Set.elements evars))
       )
    with e when CErrors.noncritical e ->
      RespError (CErrors.print e ++ spc() ++ str "(for goal "++int r_goalno ++ str ")")

  let name_of_task { t_name } = t_name
  let name_of_request { r_name } = r_name

end (* }}} *)

module TaskQueue = AsyncTaskQueue.MakeQueue(TacTask) ()

let assign_tac ~abstract res : unit Proofview.tactic =
  Proofview.(Goal.enter begin fun g ->
  let gid = Goal.goal g in
  let g_solution =
    try List.assoc gid res
    with Not_found -> CErrors.anomaly(str"Partac: wrong focus.") in
  match !g_solution with
  | None -> tclUNIT ()
  | Some (Val None) -> tclUNIT ()
  | Some (Val (Some (pt, uc))) ->
    let open Notations in
        let push_state ctx =
            Proofview.tclEVARMAP >>= fun sigma ->
            Proofview.Unsafe.tclEVARS (Evd.merge_universe_context sigma ctx)
        in
        (if abstract then Abstract.tclABSTRACT None else (fun x -> x))
            (push_state uc <*> Tactics.exact_no_check (EConstr.of_constr pt))
  | Some (Exn e) -> raise e
  end)

let enable_par ~nworkers = ComTactic.set_par_implementation
  (fun ~pstate ~info t_ast ~abstract ~with_end_tac ->
    let t_state = Vernacstate.freeze_interp_state ~marshallable:true in
    TaskQueue.with_n_workers nworkers CoqworkmgrApi.High (fun queue ->
    Declare.Proof.map pstate ~f:(fun p ->
    let open TacTask in
    let results = (Proof.data p).Proof.goals |> CList.map_i (fun i g ->
      let ans = ref None in
      TaskQueue.enqueue_task queue
      ~cancel_switch:(ref false)
      { t_state; t_assign = ans; t_ast;
          t_goalno = i; t_goal = g; t_name = Proof.goal_uid g;
          t_kill = (fun () -> TaskQueue.cancel_all queue) };
      g, ans) 1 in
    TaskQueue.join queue;
    let p,_,() =
      Proof.run_tactic (Global.env())
      (assign_tac ~abstract results) p in
    p)))
