(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Lwt.Infix

(* TODO: move away? *)
module type QueueElement = sig
  type data
  type dependency
  val is_invalid : dependency -> data -> bool
end

module MakeQueue(E : QueueElement) : sig
  val enqueue : E.data -> unit
  val dequeue : unit -> E.data Lwt.t
  val remove_invalid : E.dependency -> E.data list
end = struct

type t = E.data list ref
let queue : t = ref []
let queue_cond = Lwt_condition.create ()

let enqueue m =
  queue := !queue @ [m];
  Lwt_condition.signal queue_cond ()

let dequeue () =
  begin
    if !queue = []
    then Lwt_condition.wait queue_cond
    else Lwt.return ()
  end >>= fun () ->
  let x = List.hd !queue in
  queue := List.tl !queue;
  Lwt.return x

let remove_invalid id =
  let invalid, valid = List.partition (E.is_invalid id) !queue in
  queue := valid;
  invalid

end

open Scheduler

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type execution_status =
  | Success of Vernacstate.t option
  | Error of string Loc.located * Vernacstate.t option (* State to use for resiliency *)

let success vernac_st = Success (Some vernac_st)
let error loc msg vernac_st = Error ((loc,msg),(Some vernac_st))

type prepared_task =
  | PSkip of sentence_id
  | PExec of sentence_id * ast
  | PDelegate of sentence_id * execution_status DelegationManager.remote_mapping * prepared_task list

type job = prepared_task list * Vernacstate.t * sentence_id

module ProofWorker = DelegationManager.Make(struct
  type t = job
  let name = "proof"
  let binary_name = "vscoqtop_worker.opt"
  let pool_size = 1
end)

type event = ProofWorkerEvent of ProofWorker.event (*| TacticWorkerEvent of Declare.Proof.event*)
type events = event Lwt.t list

let inject_dm_event x : event Lwt.t =
  x >>= fun x -> Lwt.return @@ ProofWorkerEvent x

let inject_dm_events l =
  Lwt.return @@ List.map inject_dm_event l
(*
let inject_pm_event x : event Lwt.t =
  x >>= fun x -> Lwt.return @@ TacticWorkerEvent x

let inject_pm_events l =
  Lwt.return @@ List.map inject_pm_event l
*)

let handle_event = function
  | ProofWorkerEvent event -> ProofWorker.handle_event event >>= inject_dm_events
  (*| TacticWorkerEvent event -> Declare.Proof.handle_event event >>= inject_pm_events*)

let interp_ast vernac_st ast =
    Feedback.set_id_for_feedback doc_id state_id;
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let result =
      try Ok(Vernacinterp.interp ~st:vernac_st ast,[])
      with e when CErrors.noncritical e ->
        let e, info = Exninfo.capture e in
        Error (e, info) in
    Sys.(set_signal sigint Signal_ignore);
    match result with
    | Ok (vernac_st, events) ->
        log @@ "[V] Executed: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
          " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
        Lwt.return (vernac_st, success vernac_st, (*List.map inject_pm_event*) events)
    | Error (Sys.Break, _ as exn) ->
        log @@ "[V] Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        Exninfo.iraise exn
    | Error (e, info) ->
        log @@ "[V] Failed to execute: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
        let loc = Loc.get_loc info in
        let msg = CErrors.iprint (e, info) in
        Lwt.return (vernac_st, error loc (Pp.string_of_ppcmds msg) vernac_st,[])

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type feedback_message = Feedback.level * Loc.t option * Pp.t

type state = {
  initial : Vernacstate.t;
  of_sentence : ((execution_status Lwt.t * execution_status Lwt.u) * feedback_message list) SM.t;
}

type progress_hook = state option -> unit Lwt.t

let init_master vernac_state = {
  initial = vernac_state;
  of_sentence = SM.empty;
}

let find_fulfilled_opt x m =
  try
    let (p,_), _ = SM.find x m in
    match Lwt.state p with
    | Lwt.Return v -> Some v
    | Lwt.Fail exn -> assert false
    | Lwt.Sleep -> None
  with Not_found -> None

module Jobs = struct
  type data = execution_status DelegationManager.remote_mapping * (prepared_task list * Vernacstate.t * sentence_id)
  type dependency = sentence_id
  let is_invalid id (_,(_,_,id1)) = Stateid.equal id id1
end
module Queue = MakeQueue(Jobs)

let add_remote_promise (st, remote_mapping) id =
  let remote_mapping, pr = ProofWorker.lwt_remotely_wait remote_mapping id in
  ({ st with of_sentence = SM.add id (pr,[]) st.of_sentence }, remote_mapping)

let remotize doc (st,remote_mapping) id =
  match Document.get_sentence doc id with
  | None -> (st, remote_mapping), PSkip id
  | Some sentence ->
    begin match sentence.ast with
    | ValidAst (ast,_) ->
      add_remote_promise (st, remote_mapping) id, PExec(id,ast)
    | ParseError _ -> (st, remote_mapping), PSkip id
    end

let prepare_task ~progress_hook doc st task : state * prepared_task =
  match task with
  | Skip id ->
     { st with of_sentence = SM.add id (Lwt.task (), []) st.of_sentence }, PSkip id
  | Exec(id,ast) ->
     { st with of_sentence = SM.add id (Lwt.task (), []) st.of_sentence }, PExec(id,ast)
  | OpaqueProof (id,ids) ->
     let remote_mapping = ProofWorker.empty_remote_mapping ~progress_hook:(fun () -> progress_hook None) in
     let (st,remote_mapping), jobs = CList.fold_left_map (remotize doc) (st,remote_mapping) ids in
     { st with of_sentence = SM.add id (Lwt.task (), []) st.of_sentence }, PDelegate(id, remote_mapping, jobs)
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let update st id v =
  match SM.find id st.of_sentence with
  | ((_,r),_) -> Lwt.wakeup r v
  | exception Not_found -> CErrors.anomaly Pp.(str "No state for " ++ Stateid.print id)

let id_of_prepared_task = function
  | PSkip id -> id
  | PExec(id, _) -> id
  | PDelegate(id, _, _) -> id

let rec worker_main st ((job , vs, _state_id) : job) =
  (* signalling progress is automtically done by the resolution of remote
     promises *)
  Lwt_list.fold_left_s (execute ~doc_id st) (vs,[],false) job >>= fun _ ->
  Lwt.return ()

and execute ~doc_id st (vs,events,interrupted) task =
  if interrupted then begin
    update st (id_of_prepared_task task) (Error ((None,"interrupted"),None));
    Lwt.return (vs,events,true)
  end else
    try
      match task with
      | PSkip id ->
          update st id (Success (Some vs));
          Lwt.return (vs,events,false)
      | PExec (id,ast) ->
          interp_ast vs ast >>= fun (vs, v, ev) ->
          update st id v;
          Lwt.return (vs,events @ ev,false)
      | PDelegate (id, mapping, job) ->
          Queue.enqueue (mapping,(job,vs,id));
          let ast = CAst.make @@ Vernacexpr.{ expr = VernacEndProof Admitted; attrs = []; control = [] } in
          interp_ast vs ast >>= fun (vs, v, ev) ->
          update st id v;
          let e =
            ProofWorker.worker_available ~job:Queue.dequeue
              ~fork_action:(worker_main st) in
          Lwt.return (vs,events @ ev @ List.map inject_dm_event e ,false)
    with Sys.Break ->
      Lwt.return (vs,events,true)

let observe progress_hook doc id st : (state * events) Lwt.t =
  log @@ "[M] Observe " ^ Stateid.to_string id;
  let rec build_tasks id tasks =
    begin match find_fulfilled_opt id st.of_sentence with
    | Some (Success (Some vs)) ->
      (* We reached an already computed state *)
      log @@ "[M] Reached computed state " ^ Stateid.to_string id;
      vs, tasks
    | Some (Error(_,Some vs)) ->
      (* We try to be resilient to an error *)
      log @@ "[M] Error resiliency on state " ^ Stateid.to_string id;
      vs, tasks
    | _ ->
      log @@ "[M] Non (locally) computed state " ^ Stateid.to_string id;
      let (base_id, task) = task_for_sentence (Document.schedule doc) id in
      begin match base_id with
      | None -> (* task should be executed in initial state *)
        st.initial, task :: tasks
      | Some base_id ->
        build_tasks base_id (task::tasks)
      end
    end
  in
  let vs, tasks = build_tasks id [] in
  let st, tasks = CList.fold_left_map (prepare_task ~progress_hook doc) st tasks in
  (* st is now final, we could return it, but we only implement asynchronous
    fulfilling of delegated jobs *)
  let progress_hook () = progress_hook (Some st) in
  let execute_w_progress x t =
    let doc_id = Document.id_of_doc doc in
    execute ~doc_id st x t >>= fun x ->
    progress_hook () >>= fun () ->
    Lwt.return x in
  Lwt_list.fold_left_s execute_w_progress (vs,[],false) tasks >>= fun (_,events,_) ->
  Lwt.return (st,events)

(* If we don't work we have re-create a minimal state that is good enough to
   execute the sentences and send feedback. It is easier/faster than sending a
   stripped state *)
let init_worker initial_vs ids link =
  let st = init_master initial_vs in
  let remote_mapping = ProofWorker.empty_remote_mapping ~progress_hook:Lwt.return in
  let st, remote_mapping = List.fold_left add_remote_promise (st, remote_mapping) ids in
  Lwt.return (remote_mapping,st)

let get_fulfilled_opt x =
  match Lwt.state x with
  | Lwt.Return x -> Some x
  | _ -> None

let errors st =
  List.fold_left (fun acc (id, ((p,_),_)) ->
    match get_fulfilled_opt p with
    | Some (Error ((loc,e),_st)) -> (id,loc,e) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.of_sentence

let warning_of_feedback id (lvl,loc,msg) = (id,loc, Pp.string_of_ppcmds msg)

let warnings st =
  List.fold_left (fun acc (id, (_,l)) -> List.map (warning_of_feedback id) l @ acc) [] @@ SM.bindings st.of_sentence

let shift_locs st pos offset =
  (* FIXME shift loc in feedback *)
  let shift_error ((p,fb),r as orig) = match get_fulfilled_opt p with
  | Some (Error ((Some loc,e),st)) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then (Lwt.return @@ Error ((Some (Loc.shift_loc offset offset loc),e),st), fb),r
    else if stop >= pos then (Lwt.return @@ Error ((Some (Loc.shift_loc 0 offset loc),e),st), fb),r
    else orig
  | _ -> orig
  in
  { st with of_sentence = SM.map shift_error st.of_sentence }

let executed_ids st =
  SM.fold (fun id ((p,_),_) acc ->
    match get_fulfilled_opt p with
    | Some (Success _ | Error _) -> id :: acc
    | _ -> acc) st.of_sentence []

let is_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success (Some _) | Error (_,Some _)) -> true
  | _ -> false

let is_remotely_executed st id =
  match find_fulfilled_opt id st.of_sentence with
  | Some (Success None | Error (_,None)) -> true
  | _ -> false

let query id st ast = assert false

let invalidate1 of_sentence id =
  try
    let (p,_),_ = SM.find id of_sentence in
    match Lwt.state p with
    | Lwt.Sleep ->
        Lwt.cancel p;
        SM.remove id of_sentence
    | _ -> SM.remove id of_sentence
  with Not_found -> of_sentence

let rec invalidate schedule id st =
  log @@ "Invalidating: " ^ Stateid.to_string id;
  let of_sentence = invalidate1 st.of_sentence id in
  let removed = Queue.remove_invalid id in
  let of_sentence = List.fold_left invalidate1 of_sentence
    List.(concat (map (fun (_,(ptl,_,_)) -> map id_of_prepared_task ptl) removed)) in
  if of_sentence == st.of_sentence then Lwt.return st else
  let deps = Scheduler.dependents schedule id in
  Stateid.Set.fold (fun dep_id st ->
    st >>= fun st -> invalidate schedule dep_id st) deps
    (Lwt.return { st with of_sentence })

let get_parsing_state_after st id =
  Option.bind (find_fulfilled_opt id st.of_sentence)
    (function Success (Some st) | Error (_,Some st) -> Some st.Vernacstate.parsing | _ -> None)

let get_proofview st id =
  match find_fulfilled_opt id st.of_sentence with
  | None -> log "Cannot find state for proofview"; None
  | Some (Error _) -> log "Proofview requested in error state"; None
  | Some (Success None) -> log "Proofview requested in a remotely checked state"; None
  | Some (Success (Some { Vernacstate.lemmas = None; _ })) -> log "Proofview requested in a state with no proof"; None
  | Some (Success (Some { Vernacstate.lemmas = Some st; _ })) ->
      log "Proofview is there";
      (* nicely designed API: Proof is both a file and a deprecated module *)
      let open Proof in
      let open Declare in
      let open Vernacstate in
      st |> LemmaStack.with_top ~f:Proof.get |> data |> Option.make

let handle_feedback state_id contents st =
  match contents with
  | Feedback.Message(lvl,loc,msg) ->
    begin match SM.find_opt state_id st.of_sentence with
    | None -> log @@ "Received feedback on non-existing state id " ^ Stateid.to_string state_id; st
    | Some (p,l) ->
      let of_sentence = SM.add state_id (p, (lvl,loc,msg) :: l) st.of_sentence in
      { st with of_sentence }
    end
  | _ -> st

module WorkerProcess = struct
  type options = ProofWorker.options
  let parse_options = ProofWorker.parse_options
  let main ~st:initial_vernac_state options =
    ProofWorker.setup_plumbing options >>= fun (mapping, link, job) ->
    init_worker initial_vernac_state mapping link >>= fun (remote_mapping,state) ->
    ProofWorker.new_process_worker remote_mapping link;
    worker_main state job
end
