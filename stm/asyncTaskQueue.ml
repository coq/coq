(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Pp
open Util

let pr_err s = Printf.eprintf "%s] %s\n" (System.process_id ()) s; flush stderr

let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

module type Task = sig

  type task

  (* Marshallable *)
  type request
  type response

  val name : string (* UID of the task kind, for -toploop *)
  val extra_env : unit -> string array

  (* run by the master, on a thread *)
  val request_of_task : [ `Fresh | `Old ] -> task -> request option
  val use_response : task -> response -> [ `Stay | `StayReset ]
  val on_marshal_error : string -> task -> unit
  val on_slave_death : task option -> [ `Exit of int | `Stay ]
  val on_task_cancellation_or_expiration : task option -> unit
  val forward_feedback : Stateid.t -> Feedback.feedback_content -> unit
 
  (* run by the worker *)
  val perform : request -> response

  (* debugging *)
  val name_of_task : task -> string
  val name_of_request : request -> string

end

type cancel_switch = bool ref

module Make(T : Task) = struct

  module Worker = Spawn.Sync(struct 
    let add_timeout ~sec f =
      ignore(Thread.create (fun () ->
        while true do
          Unix.sleep sec;
          if not (f ()) then Thread.exit ()
        done)
      ())
  end)
  
  module WorkersPool = WorkerPool.Make(Worker)

  let queue : (T.task * cancel_switch) TQueue.t = TQueue.create ()

  let enqueue_task t c =
    prerr_endline ("Enqueue task "^T.name_of_task t);
    TQueue.push queue (t,c)

  let cancel_worker = WorkersPool.cancel

  type request = Request of T.request

  let name_of_request (Request r) = T.name_of_request r

  type response =
    | Response of T.response
    | RespFeedback of Feedback.feedback
    | RespGetCounterNewUnivLevel

  type more_data =
    | MoreDataUnivLevel of Univ.universe_level list
 
  let request_cswitch_of_task (t, c) = T.request_of_task t, c
  
  let slave_respond msg = match msg with Request r -> Response (T.perform r)

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
    try (Marshal.from_channel ic : request)
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
    try (Marshal.from_channel ic : more_data)
    with Failure s | Invalid_argument s | Sys_error s ->
      marshal_err ("unmarshal_more_data: "^s)

  let set_order cmp = TQueue.set_order queue (fun (t1,_) (t2,_) -> cmp t1 t2)

  let join () =
    if not (WorkersPool.is_empty ()) then
      TQueue.wait_until_n_are_waiting_and_queue_empty
        (WorkersPool.n_workers ()) queue
  let cancel_all () =
    TQueue.clear queue;
    WorkersPool.cancel_all ()

  exception KillRespawn
  exception Die
  exception Expired
    
  let report_status ?(id = !Flags.async_proofs_worker_id) s =
    Pp.feedback ~state_id:Stateid.initial (Feedback.SlaveStatus(id, s))

  let rec manage_slave ~cancel:cancel_user_req ~die id respawn =
    let ic, oc, proc =
      let rec set_slave_opt = function
        | [] -> !Flags.async_proofs_flags_for_workers @
                ["-toploop"; T.name^"top";
                 "-worker-id"; id;
                 "-async-proofs-worker-priority";
                   Flags.string_of_priority !Flags.async_proofs_worker_priority]
        | ("-ideslave"|"-emacs"|"-emacs-U"|"-batch")::tl -> set_slave_opt tl
        | ("-async-proofs" |"-toploop" |"-vi2vo" |"-compile"
          |"-load-vernac-source" |"-compile-verbose"
          |"-async-proofs-worker-priority" |"-worker-id") :: _ :: tl ->
          set_slave_opt tl
        | x::tl -> x :: set_slave_opt tl in
      let args =
        Array.of_list (set_slave_opt (List.tl (Array.to_list Sys.argv))) in
      let env = Array.append (T.extra_env ()) (Unix.environment ()) in
      respawn ~args ~env () in
    let last_task = ref None in
    let task_expired = ref false in
    let task_cancelled = ref false in
    let worker_age = ref `Fresh in
    let got_token = ref false in
    let giveback_token () =
      if !got_token then (CoqworkmgrApi.giveback 1; got_token := false) in
    CThread.prepare_in_channel_for_thread_friendly_io ic;
    try
      while not !die do
        prerr_endline "waiting for a task";
        report_status ~id "Idle";
        let task, cancel_switch = TQueue.pop queue in
        prerr_endline ("got task: "^T.name_of_task task);
        last_task := Some task;
        begin try
          let req = T.request_of_task !worker_age task in
          if req = None then raise Expired;
          ignore(CoqworkmgrApi.get 1); got_token := true;
          prerr_endline ("got execution token");
          marshal_request oc (Request (Option.get req));
          Worker.kill_if proc ~sec:1 (fun () ->
            task_expired := !cancel_switch;
            task_cancelled := !cancel_user_req;
            if !cancel_user_req then cancel_user_req := false;
            !task_expired || !task_cancelled || !die);
          let rec loop () =
            let response = unmarshal_response ic in
            match response with
            | Response resp ->
                (match T.use_response task resp with
                | `Stay ->
                     last_task := None; worker_age := `Old; giveback_token ()
                | `StayReset -> last_task := None; raise KillRespawn)
            | RespGetCounterNewUnivLevel ->
                marshal_more_data oc (MoreDataUnivLevel
                  (CList.init 10 (fun _ ->
                     Universes.new_univ_level (Global.current_dirpath ()))));
                loop ()
            | RespFeedback ({ Feedback.id = Feedback.State state_id } as fbk) ->
                T.forward_feedback state_id fbk.Feedback.content;
                loop ()
            | RespFeedback _ -> Errors.anomaly (str"Parsing in master process")
          in
            loop ()
        with
        | Expired -> prerr_endline ("Task expired: " ^ T.name_of_task task)
        | (Sys_error _|Invalid_argument _|End_of_file|KillRespawn) as e ->
            raise e (* we pass the exception to the external handler *)
        | MarshalError s -> T.on_marshal_error s task
        | e ->
            pr_err ("Uncaught exception in worker manager: "^
              string_of_ppcmds (print e));
            flush_all ()
        end;
      done;
      raise Die
    with
    | KillRespawn ->
        giveback_token ();
        Worker.kill proc; ignore(Worker.wait proc);
        manage_slave ~cancel:cancel_user_req ~die id respawn
    | (Die | TQueue.BeingDestroyed) ->
        giveback_token ();
        Worker.kill proc;ignore(Worker.wait proc)
    | Sys_error _ | Invalid_argument _ | End_of_file when !task_expired ->
        giveback_token ();
        T.on_task_cancellation_or_expiration !last_task;
        ignore(Worker.wait proc);
        manage_slave ~cancel:cancel_user_req ~die id respawn
    | Sys_error _ | Invalid_argument _ | End_of_file when !task_cancelled ->
        giveback_token ();
        msg_warning(strbrk "The worker was cancelled.");
        T.on_task_cancellation_or_expiration !last_task;
        Worker.kill proc; ignore(Worker.wait proc);
        manage_slave ~cancel:cancel_user_req ~die id respawn
    | Sys_error _ | Invalid_argument _ | End_of_file ->
        giveback_token ();
        match T.on_slave_death !last_task with
        | `Stay -> 
            msg_warning(strbrk "The worker process died badly.");
            Worker.kill proc; ignore(Worker.wait proc);
            manage_slave ~cancel:cancel_user_req ~die id respawn
        | `Exit exit_code ->
            Worker.kill proc;
            let exit_status proc = match Worker.wait proc with
              | Unix.WEXITED 0x400 -> "exit code unavailable"
              | Unix.WEXITED i -> Printf.sprintf "exit(%d)" i
              | Unix.WSIGNALED sno -> Printf.sprintf "signalled(%d)" sno
              | Unix.WSTOPPED sno -> Printf.sprintf "stopped(%d)" sno in
            pr_err ("Fatal worker error: " ^ (exit_status proc));
            flush_all (); exit exit_code

  let slave_ic = ref stdin
  let slave_oc = ref stdout

  let slave_init_stdout () =
    let ic, oc = Spawned.get_channels () in
    slave_oc := oc; slave_ic := ic

  let bufferize f =
    let l = ref [] in
    fun () ->
      match !l with
      | [] -> let data = f () in l := List.tl data; List.hd data
      | x::tl -> l := tl; x

  let slave_handshake () = WorkersPool.worker_handshake !slave_ic !slave_oc

  let slave_main_loop reset =
    let feedback_queue = ref [] in
    let slave_feeder oc fb =
      match fb.Feedback.content with
      | Feedback.Goals _ -> feedback_queue := fb :: !feedback_queue
      | _ -> Marshal.to_channel oc (RespFeedback fb) []; flush oc in
    let flush_feeder oc =
      List.iter (fun fb -> Marshal.to_channel oc (RespFeedback fb) [])
        !feedback_queue;
      feedback_queue := [];
      flush oc in
    Pp.set_feeder (slave_feeder !slave_oc);
    Pp.log_via_feedback ();
    Universes.set_remote_new_univ_level (bufferize (fun () ->
      marshal_response !slave_oc RespGetCounterNewUnivLevel;
      match unmarshal_more_data !slave_ic with
      | MoreDataUnivLevel l -> l));
    let working = ref false in
    slave_handshake ();
    while true do
      try
        working := false;
        let request = unmarshal_request !slave_ic in
        working := true;
        report_status (name_of_request request);
        let response = slave_respond request in
        flush_feeder !slave_oc;
        report_status "Idle";
        marshal_response !slave_oc response;
        reset ()
      with
      | MarshalError s ->
        pr_err ("Fatal marshal error: " ^ s); flush_all (); exit 2
      | End_of_file ->
        prerr_endline "connection lost"; flush_all (); exit 2
      | e ->
        pr_err ("Slave: critical exception: " ^ Pp.string_of_ppcmds (print e));
        flush_all (); exit 1
    done

  let dump () =
    assert(WorkersPool.is_empty ()); (* ATM, we allow that only if no slaves *)
    List.map fst (TQueue.dump queue)

  let init n =
    WorkersPool.init n manage_slave
      (fun n -> Printf.sprintf "%s:%d" T.name n)
  let destroy () =
    WorkersPool.destroy ();
    TQueue.destroy queue

  let with_n_workers n f =
    try init n; let rc = f ~join ~cancel_all in destroy (); rc
    with e -> let e = Errors.push e in destroy (); raise e

  let n_workers = WorkersPool.n_workers

end
