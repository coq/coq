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

let interp_ast vernac_st ast =
  try
    Sys.(set_signal sigint (Signal_handle(fun _ -> raise Break)));
    let vernac_st = Vernacinterp.interp ~st:vernac_st ast in (* TODO set status to "Delegated" *)
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Executed: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast) ^
      " (" ^ (if Option.is_empty vernac_st.Vernacstate.lemmas then "no proof" else "proof")  ^ ")";
    vernac_st, success vernac_st
  with
  | Sys.Break as exn ->
    let exn = Exninfo.capture exn in
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Interrupted executing: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    Exninfo.iraise exn
  | any ->
    let (e, info) = Exninfo.capture any in
    Sys.(set_signal sigint Signal_ignore);
    log @@ "[V] Failed to execute: " ^ (Pp.string_of_ppcmds @@ Ppvernac.pr_vernac ast);
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    vernac_st, error loc (Pp.string_of_ppcmds msg) vernac_st

type sentence_id = Stateid.t
type ast = Vernacexpr.vernac_control

module SM = Map.Make (Stateid)

type state = {
  initial : Vernacstate.t;
  of_sentence : (execution_status Lwt.t * execution_status Lwt.u) SM.t;
}

type progress_hook = state option -> unit Lwt.t

let init vernac_state = {
  initial = vernac_state;
  of_sentence = SM.empty;
}

let find_fulfilled_opt x m =
  try
    let p, _ = SM.find x m in
    match Lwt.state p with
    | Lwt.Return v -> Some v
    | Lwt.Fail exn -> assert false
    | Lwt.Sleep -> None
  with Not_found -> None

type prepared_task =
  | PSkip of sentence_id
  | PExec of sentence_id * ast
  | PDelegate of sentence_id * execution_status DelegationManager.remote_mapping * prepared_task list

module Jobs = struct
  type data = execution_status DelegationManager.remote_mapping * (prepared_task list * Vernacstate.t * sentence_id)
  type dependency = sentence_id
  let is_invalid id (_,(_,_,id1)) = Stateid.equal id id1
end
module Queue = MakeQueue(Jobs)

let remotize doc (st,remote_mapping) id =
  match Document.get_sentence doc id with
  | None -> (st, remote_mapping), PSkip id
  | Some sentence ->
    begin match sentence.ast with
    | ValidAst (ast,_) ->
      let remote_mapping, pr = DelegationManager.lwt_remotely_wait remote_mapping in
      ({ st with of_sentence = SM.add id pr st.of_sentence }, remote_mapping), PExec(id,ast)
    | ParseError _ -> (st, remote_mapping), PSkip id
    end

let new_process_worker st mapping link =
  DelegationManager.new_process_worker mapping link;
  st

let prepare_task ~progress_hook doc st task : state * prepared_task =
  match task with
  | Skip id ->
     { st with of_sentence = SM.add id (Lwt.task ()) st.of_sentence }, PSkip id
  | Exec(id,ast) ->
     { st with of_sentence = SM.add id (Lwt.task ()) st.of_sentence }, PExec(id,ast)
  | OpaqueProof (id,ids) ->
     let remote_mapping = DelegationManager.empty_remote_mapping ~progress_hook:(fun () -> progress_hook None) in
     let (st,remote_mapping), jobs = CList.fold_left_map (remotize doc) (st,remote_mapping) ids in
     { st with of_sentence = SM.add id (Lwt.task ()) st.of_sentence }, PDelegate(id, remote_mapping, jobs)
  | _ -> CErrors.anomaly Pp.(str "task not supported yet")

let update st id v =
  match SM.find id st.of_sentence with
  | (_,r) -> Lwt.wakeup r v
  | exception Not_found -> CErrors.anomaly Pp.(str "No state for " ++ Stateid.print id)

let id_of_prepared_task = function
  | PSkip id -> id
  | PExec(id, _) -> id
  | PDelegate(id, _, _) -> id

type job = prepared_task list * Vernacstate.t * sentence_id

let rec worker_main st ((job , vs, _state_id) : job) =
  (* signalling progress is automtically done by the resolution of remote
     promises *)
  Lwt_list.fold_left_s (execute st) (vs,[],false) job >>= fun _ ->
  Lwt.return ()

and execute st (vs,events,interrupted) task =
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
          let vs, v = interp_ast vs ast in
          update st id v;
          Lwt.return (vs,events,false)
      | PDelegate (id, mapping, job) ->
          Queue.enqueue (mapping,(job,vs,id));
          let ast = CAst.make @@ Vernacexpr.{ expr = VernacEndProof Admitted; attrs = []; control = [] } in
          let vs, v = interp_ast vs ast in
          update st id v;
          let e =
            DelegationManager.worker_available st ~job:Queue.dequeue
              ~fork_action:worker_main
              ~process_action:"vscoqtop_worker.opt" in
          Lwt.return (vs,events @ e,false)
    with Sys.Break ->
      Lwt.return (vs,events,true)

let observe progress_hook doc id st : (state * 'a DelegationManager.events) Lwt.t =
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
    execute st x t >>= fun x ->
    progress_hook () >>= fun () ->
    Lwt.return x in
  Lwt_list.fold_left_s execute_w_progress (vs,[],false) tasks >>= fun (_,events,_) ->
  Lwt.return (st,events)

let get_fulfilled_opt x =
  match Lwt.state x with
  | Lwt.Return x -> Some x
  | _ -> None

let errors st =
  List.fold_left (fun acc (id, (p,_)) ->
    match get_fulfilled_opt p with
    | Some (Error ((loc,e),_st)) -> (id,loc,e) :: acc
    | _ -> acc)
    [] @@ SM.bindings st.of_sentence

let shift_locs st pos offset =
  let shift_error (p,r as orig) = match get_fulfilled_opt p with
  | Some (Error ((Some loc,e),st)) ->
    let (start,stop) = Loc.unloc loc in
    if start >= pos then (Lwt.return @@ Error ((Some (Loc.shift_loc offset offset loc),e),st)),r
    else if stop >= pos then (Lwt.return @@ Error ((Some (Loc.shift_loc 0 offset loc),e),st)),r
    else orig
  | _ -> orig
  in
  { st with of_sentence = SM.map shift_error st.of_sentence }

let executed_ids st =
  SM.fold (fun id (p,_) acc ->
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
    let p,_ = SM.find id of_sentence in
    match Lwt.state p with
    | Lwt.Sleep ->
        Lwt.cancel p; (* TODO: hook worker killing or job dequeue, eg Lwt.on_cancel  *)
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