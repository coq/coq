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

let stm_pr_err s  = Format.eprintf "%s] %s\n%!"     (Spawned.process_id ()) s

type response =
  | RespBuiltSubProof of (Constr.constr * UState.t)
  | RespError of bool * Pp.t
  | RespKilled of int
  | RespNoProgress

module TacTask : sig

  type nonrec response = response

  type task = {
    t_state    : Vernacstate.t;
    t_assign   : response option ref;
    t_ast      : ComTactic.interpretable;
    t_goalno   : int;
    t_goal     : Evar.t;
    t_kill     : unit -> unit;
    t_name     : string }

  include AsyncTaskQueue.Task with type task := task and type response := response

end = struct (* {{{ *)

  let forward_feedback { Feedback.doc_id = did; span_id = id; route; contents } =
    Feedback.feedback ~did ~id ~route contents

  type nonrec response = response

  type task = {
    t_state    : Vernacstate.t;
    t_assign   : response option ref;
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

  let name = "tactic"
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
    assign t_assign resp;
    let kill = match resp with
    | RespNoProgress | RespBuiltSubProof _ -> false
    | RespError _ -> true
    | RespKilled _ -> assert false
    in
    if kill then t_kill ();
    `Stay ((),[])

  let on_marshal_error err { t_name } =
    stm_pr_err ("Fatal marshal error: " ^ t_name );
    flush_all (); exit 1

  let on_task_cancellation_or_expiration_or_slave_death = function
    | Some { t_goalno; t_assign; t_kill } ->
      t_kill ();
      assert (Option.is_empty !t_assign);
      t_assign := Some (RespKilled t_goalno)
    | _ -> ()

  let command_focus = Proof.new_focus_kind "partac_focus"
  let focus_cond = Proof.no_cond command_focus

  let state = ref None
  let receive_state = function
    | None -> ()
    | Some st -> state := Some st

  let perform { r_state = st; r_ast = tactic; r_goal; r_goalno } =
    receive_state st;
    Vernacstate.unfreeze_full_state (Option.get !state);
    try
      Vernacstate.LemmaStack.with_top (Option.get (Option.get !state).Vernacstate.interp.lemmas) ~f:(fun pstate ->
          let pstate =
            Declare.Proof.map pstate ~f:(Proof.focus focus_cond () r_goalno) in
          let pstate =
            ComTactic.solve ~pstate
              Goal_select.SelectAll ~info:None tactic ~with_end_tac:false in
          let { Proof.sigma } = Declare.Proof.fold pstate ~f:Proof.data in
          let EvarInfo evi = Evd.find sigma r_goal in
          match Evd.(evar_body evi) with
          | Evd.Evar_empty -> RespNoProgress
          | Evd.Evar_defined t ->
              let t = Evarutil.nf_evar sigma t in
              let evars = Evarutil.undefined_evars_of_term sigma t in
              if Evar.Set.is_empty evars then
                let t = EConstr.Unsafe.to_constr t in
                RespBuiltSubProof (t, Evd.ustate sigma)
              else
                CErrors.user_err
                  Pp.(str"The par: selector requires a tactic that makes no progress or fully" ++
                      str" solves the goal and leaves no unresolved existential variables. The following" ++
                      str" existentials remain unsolved: " ++ prlist (Termops.pr_existential_key (Global.env ()) sigma) (Evar.Set.elements evars))
       )
    with e ->
      let noncrit = CErrors.noncritical e in
      RespError (noncrit, CErrors.print e ++ spc() ++ str "(for goal "++int r_goalno ++ str ")")

  let perform r : response =
    NewProfile.profile "partac.perform"
      ~args:(fun () -> ["goalno", `Intlit (string_of_int r.r_goalno)])
      (fun () -> perform r)
      ()

  let name_of_task { t_name } = t_name
  let name_of_request { r_name } = r_name

end (* }}} *)

module TaskQueue = AsyncTaskQueue.MakeQueue(TacTask) ()

let assign_tac ~abstract res : unit Proofview.tactic =
  Proofview.(Goal.enter begin fun g ->
  let gid = Goal.goal g in
  match  List.assoc gid res with
  | exception Not_found -> (* No progress *) tclUNIT ()
  | (pt, uc) ->
    let open Notations in
    let push_state ctx =
      Proofview.tclEVARMAP >>= fun sigma ->
      Proofview.Unsafe.tclEVARS (Evd.merge_universe_context sigma ctx)
    in
    (if abstract then Abstract.tclABSTRACT None else (fun x -> x))
      (push_state uc <*> Tactics.exact_no_check (EConstr.of_constr pt))
  end)

let get_results res =
  (* If one of the goals failed others may be missing results, so we
     need to check for RespError before complaining about missing
     results. Also if there are non-RespKilled errors we prefer to
     report them. *)
  let missing = ref [] in
  let killed = ref [] in
  let res = CList.map_filter_i (fun i (g,v) -> match !v with
      | None -> missing := (succ i) :: !missing; None
      | Some (RespBuiltSubProof v) -> Some (g,v)
      | Some RespNoProgress -> None
      | Some (RespKilled goalno) -> killed := goalno :: !killed; None
      | Some (RespError (noncrt, msg)) ->
        if noncrt then raise (AsyncTaskQueue.RemoteException msg)
        else CErrors.anomaly msg)
      res
  in
  match !killed, !missing with
  | [], [] -> res
  | killed :: _, _ -> CErrors.anomaly Pp.(str "Worker failed (for goal " ++ int killed ++ str")")
  | [], missing ->
    CErrors.anomaly
      (str "Missing results (for " ++
       str (CString.plural (List.length missing) "goal") ++
       spc () ++ prlist_with_sep spc int missing ++ str ")")

let enable_par ~spawn_args ~nworkers = ComTactic.set_par_implementation
  (fun ~pstate ~info t_ast ~abstract ~with_end_tac ->
    let t_state = Vernacstate.freeze_full_state () in
    let t_state = Vernacstate.Stm.make_shallow t_state in
    TaskQueue.with_n_workers ~spawn_args nworkers CoqworkmgrApi.High (fun queue ->
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
    let results = get_results results in
    let p,_,() =
      NewProfile.profile "partac.assign" (fun () ->
          Proof.run_tactic (Global.env())
            (assign_tac ~abstract results) p)
        ()
    in
    p)))
