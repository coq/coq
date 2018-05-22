(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Pp
open Util

let stm_pr_err pp = Format.eprintf "%s] @[%a@]\n%!" (Spawned.process_id ()) Pp.pp_with pp
let stm_prerr_endline s = if !Flags.debug then begin stm_pr_err (str s) end else ()

type cancel_switch = bool ref
let async_proofs_flags_for_workers = ref []

module type Task = sig

  type task
  type competence

  type worker_status = Fresh | Old of competence

  (* Marshallable *)
  type request
  type response

  val name : string ref (* UID of the task kind, for -toploop *)
  val extra_env : unit -> string array

  (* run by the master, on a thread *)
  val request_of_task : worker_status -> task -> request option
  val task_match : worker_status -> task -> bool
  val use_response : worker_status -> task -> response ->
    [ `Stay of competence * task list | `End ]
  val on_marshal_error : string -> task -> unit
  val on_task_cancellation_or_expiration_or_slave_death : task option -> unit
  val forward_feedback : Feedback.feedback -> unit

  (* run by the worker *)
  val perform : request -> response

  (* debugging *)
  val name_of_task : task -> string
  val name_of_request : request -> string

end

module Make(T : Task) () = struct

  exception Die
  type response =
    | Response of T.response
    | RespFeedback of Feedback.feedback
    | RespGetCounterNewUnivLevel
  type request = Request of T.request

  type more_data =
    | MoreDataUnivLevel of UnivGen.universe_id list

  let slave_respond (Request r) =
    let res = T.perform r in
    Response res

  exception MarshalError of string

  let marshal_to_channel oc data =
    Marshal.to_channel oc data [];
    flush oc

  let marshal_err s = raise (MarshalError s)

  let marshal_request oc (req : request) =
    try marshal_to_channel oc req
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("marshal_request: "^s)

  let unmarshal_request ic =
    try (CThread.thread_friendly_input_value ic : request)
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("unmarshal_request: "^s)

  let marshal_response oc (res : response) =
    try marshal_to_channel oc res
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("marshal_response: "^s)

  let unmarshal_response ic =
    try (CThread.thread_friendly_input_value ic : response)
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("unmarshal_response: "^s)

  let marshal_more_data oc (res : more_data) =
    try marshal_to_channel oc res
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("marshal_more_data: "^s)

  let unmarshal_more_data ic =
    try (CThread.thread_friendly_input_value ic : more_data)
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("unmarshal_more_data: "^s)

  let report_status ?(id = !Flags.async_proofs_worker_id) s =
    let open Feedback in
    feedback ~id:Stateid.initial (WorkerStatus(id, s))

  module Worker = Spawn.Sync ()

  module Model = struct

  type process = Worker.process
  type extra = (T.task * cancel_switch) TQueue.t

  let spawn id =
    let name = Printf.sprintf "%s:%d" !T.name id in
    let proc, ic, oc =
      let rec set_slave_opt = function
        | [] -> !async_proofs_flags_for_workers @
                ["-worker-id"; name;
                 "-async-proofs-worker-priority";
                   CoqworkmgrApi.(string_of_priority !async_proofs_worker_priority)]
        | ("-emacs"|"-emacs-U"|"-batch")::tl -> set_slave_opt tl
        | ("-async-proofs" |"-vio2vo"
          |"-load-vernac-source" |"-l" |"-load-vernac-source-verbose" |"-lv"
          |"-compile" |"-compile-verbose"
          |"-async-proofs-worker-priority" |"-worker-id") :: _ :: tl ->
          set_slave_opt tl
        | x::tl -> x :: set_slave_opt tl in
      let args =
        Array.of_list (set_slave_opt (List.tl (Array.to_list Sys.argv))) in
      let env = Array.append (T.extra_env ()) (Unix.environment ()) in
    let worker_name = System.get_toplevel_path ("coq" ^ !T.name) in
    Worker.spawn ~env worker_name args in
    name, proc, CThread.prepare_in_channel_for_thread_friendly_io ic, oc

  let manager cpanel (id, proc, ic, oc) =
    let { WorkerPool.extra = queue; exit; cancelled } = cpanel in
    let exit () =  report_status ~id "Dead"; exit () in
    let last_task = ref None in
    let worker_age = ref T.Fresh in
    let got_token = ref false in
    let giveback_exec_token () =
      if !got_token then (CoqworkmgrApi.giveback 1; got_token := false) in
    let stop_waiting = ref false in
    let expiration_date = ref (ref false) in
    let pick_task () =
      stm_prerr_endline "waiting for a task";
      let pick age (t, c) = not !c && T.task_match age t in
      let task, task_expiration =
        TQueue.pop ~picky:(pick !worker_age) ~destroy:stop_waiting queue in
      expiration_date := task_expiration;
      last_task := Some task;
      stm_prerr_endline ("got task: " ^ T.name_of_task task);
      task in
    let add_tasks l =
      List.iter (fun t -> TQueue.push queue (t,!expiration_date)) l in
    let get_exec_token () =
      ignore(CoqworkmgrApi.get 1);
      got_token := true;
      stm_prerr_endline ("got execution token") in
    let kill proc =
      Worker.kill proc;
      stm_prerr_endline ("Worker exited: " ^
        match Worker.wait proc with
        | Unix.WEXITED 0x400 -> "exit code unavailable"
        | Unix.WEXITED i -> Printf.sprintf "exit(%d)" i
        | Unix.WSIGNALED sno -> Printf.sprintf "signalled(%d)" sno
        | Unix.WSTOPPED sno -> Printf.sprintf "stopped(%d)" sno) in
    let more_univs n =
      CList.init n (fun _ -> UnivGen.new_univ_id ()) in

    let rec kill_if () =
      if not (Worker.is_alive proc) then ()
      else if cancelled () || !(!expiration_date) then
        let () = stop_waiting := true in
        let () = TQueue.broadcast queue in
        Worker.kill proc
      else
        let () = Unix.sleep 1 in
        kill_if ()
    in
    let kill_if () =
      try kill_if ()
      with Sys.Break ->
        let () = stop_waiting := true in
        let () = TQueue.broadcast queue in
        Worker.kill proc
    in
    let _ = Thread.create kill_if () in

    try while true do
      report_status ~id "Idle";
      let task = pick_task () in
      match T.request_of_task !worker_age task with
      | None -> stm_prerr_endline ("Task expired: " ^ T.name_of_task task)
      | Some req ->
      try
        get_exec_token ();
        marshal_request oc (Request req);
        let rec continue () =
          match unmarshal_response ic with
          | RespGetCounterNewUnivLevel ->
              marshal_more_data oc (MoreDataUnivLevel (more_univs 10));
              continue ()
          | RespFeedback fbk -> T.forward_feedback fbk; continue ()
          | Response resp ->
              match T.use_response !worker_age task resp with
              | `End -> raise Die
              | `Stay(competence, new_tasks) ->
                   last_task := None;
                   giveback_exec_token ();
                   worker_age := T.Old competence;
                   add_tasks new_tasks
        in
          continue ()
      with
      | (Sys_error _|Invalid_argument _|End_of_file|Die) as e ->
          raise e (* we pass the exception to the external handler *)
      | MarshalError s -> T.on_marshal_error s task; raise Die
      | e ->
          stm_pr_err Pp.(seq [str "Uncaught exception in worker manager: "; print e]);
          flush_all (); raise Die
    done with
    | (Die | TQueue.BeingDestroyed) ->
        giveback_exec_token (); kill proc; exit ()
    | Sys_error _ | Invalid_argument _ | End_of_file ->
        T.on_task_cancellation_or_expiration_or_slave_death !last_task;
        giveback_exec_token (); kill proc; exit ()
  end

  module Pool = WorkerPool.Make(Model)

  type queue = {
    active : Pool.pool;
    queue : (T.task * cancel_switch) TQueue.t;
    cleaner : Thread.t option;
  }

  let create size =
    let cleaner queue =
      while true do
        try ignore(TQueue.pop ~picky:(fun (_,cancelled) -> !cancelled) queue)
        with TQueue.BeingDestroyed -> Thread.exit ()
      done in
    let queue = TQueue.create () in
    {
      active = Pool.create queue ~size;
      queue;
      cleaner = if size > 0 then Some (Thread.create cleaner queue) else None;
    }

  let destroy { active; queue } =
    Pool.destroy active;
    TQueue.destroy queue

  let broadcast { queue } = TQueue.broadcast queue

  let enqueue_task { queue; active } t ~cancel_switch =
    stm_prerr_endline ("Enqueue task "^T.name_of_task t);
    TQueue.push queue (t, cancel_switch)

  let cancel_worker { active } n = Pool.cancel n active

  let name_of_request (Request r) = T.name_of_request r

  let set_order { queue } cmp =
    TQueue.set_order queue (fun (t1,_) (t2,_) -> cmp t1 t2)

  let join { queue; active } =
    if not (Pool.is_empty active) then
      TQueue.wait_until_n_are_waiting_and_queue_empty
        (Pool.n_workers active + 1(*cleaner*))
        queue

  let cancel_all { queue; active } =
    TQueue.clear queue;
    Pool.cancel_all active

  let slave_ic = ref None
  let slave_oc = ref None

  let init_stdout () =
    let ic, oc = Spawned.get_channels () in
    slave_oc := Some oc; slave_ic := Some ic

  let bufferize f =
    let l = ref [] in
    fun () ->
      match !l with
      | [] -> let data = f () in l := List.tl data; List.hd data
      | x::tl -> l := tl; x

  let slave_handshake () =
    Pool.worker_handshake (Option.get !slave_ic) (Option.get !slave_oc)

  let pp_pid pp = Pp.(str (Spawned.process_id () ^ " ") ++ pp)

  let debug_with_pid = Feedback.(function
    | { contents = Message(Debug, loc, pp) } as fb ->
       { fb with contents = Message(Debug,loc, pp_pid pp) }
    | x -> x)

  let main_loop () =
    (* We pass feedback to master *)
    let slave_feeder oc fb =
      Marshal.to_channel oc (RespFeedback (debug_with_pid fb)) []; flush oc in
    ignore (Feedback.add_feeder (fun x -> slave_feeder (Option.get !slave_oc) x));
    (* We ask master to allocate universe identifiers *)
    UnivGen.set_remote_new_univ_id (bufferize (fun () ->
      marshal_response (Option.get !slave_oc) RespGetCounterNewUnivLevel;
      match unmarshal_more_data (Option.get !slave_ic) with
      | MoreDataUnivLevel l -> l));
    let working = ref false in
    slave_handshake ();
    while true do
      try
        working := false;
        let request = unmarshal_request (Option.get !slave_ic) in
        working := true;
        report_status (name_of_request request);
        let response = slave_respond request in
        report_status "Idle";
        marshal_response (Option.get !slave_oc) response;
        CEphemeron.clear ()
      with
      | MarshalError s ->
        stm_pr_err Pp.(prlist str ["Fatal marshal error: "; s]); flush_all (); exit 2
      | End_of_file ->
        stm_prerr_endline "connection lost"; flush_all (); exit 2
      | e ->
        stm_pr_err Pp.(seq [str "Slave: critical exception: "; print e]);
        flush_all (); exit 1
    done

  let clear { queue; active } =
    assert(Pool.is_empty active); (* We allow that only if no slaves *)
    TQueue.clear queue

  let snapshot { queue; active } =
    List.map fst
     (TQueue.wait_until_n_are_waiting_then_snapshot
       (Pool.n_workers active) queue)

  let with_n_workers n f =
    let q = create n in
    try let rc = f q in destroy q; rc
    with e -> let e = CErrors.push e in destroy q; iraise e

  let n_workers { active } = Pool.n_workers active

end

module MakeQueue(T : Task) () = struct include Make(T) () end
module MakeWorker(T : Task) () = struct include Make(T) () end
