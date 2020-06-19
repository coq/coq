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

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type link = {
  write_to :  Lwt_io.output_channel;
  read_from:  Lwt_io.input_channel;
}

type ('a,'b) corresponding = { on_worker : 'b; on_master : 'a }

type 'a remote_mapping = {
  taskno : int;
  taskmap : ('a Lwt.u, 'a Lwt.t) corresponding Int.Map.t;
  progress_hook : unit -> unit Lwt.t
}

let empty_remote_mapping ~progress_hook = {
  taskno = 0;
  taskmap = Int.Map.empty;
  progress_hook;
}

(* Reads values from the worker and passes them to the resolvers in master *)
let new_manager : 'a remote_mapping -> link -> unit = fun remote_mapping link ->
  log @@ "[M] installing manager";
  let rec main () =
    Lwt_io.read_value link.read_from >>= fun (i,v) ->
    let resolver = Int.Map.find i remote_mapping.taskmap in
    log @@ "[M] Manager fulfilling " ^ string_of_int i;
    Lwt.wakeup_later resolver.on_master v;
    remote_mapping.progress_hook () >>= fun () ->
    main ()
  in
    Lwt.async_exception_hook := (fun x ->
      log @@ "[M] Manager terminated " ^ Printexc.to_string x); (* HACK *)
    Lwt.async @@ main
;;

(* Reads values from the local premises and writes them to master *)
let new_worker : 'a remote_mapping -> link -> unit = fun remote_mapping link ->
  let m = Lwt_mutex.create () in
  log @@ "[W] installing async fulfillers";
  Lwt.async_exception_hook := (fun x ->
    log @@ "[W] Worker terminated " ^ Printexc.to_string x); (* HACK *)
  Int.Map.iter (fun i { on_worker } ->
    Lwt.async @@ (fun () -> on_worker >>= fun v ->
      Lwt_mutex.with_lock m (fun () ->
        log @@ "[W] Remote fulfilling of " ^ string_of_int i;
        Lwt_io.write_value link.write_to (i,v) >>= fun () ->
        Lwt_io.flush_all ())
    )
  ) remote_mapping.taskmap
;;

(* Like Lwt.wait but the resolved is remote_mapping, via IPC *)
let lwt_remotely_wait (r : 'a remote_mapping) :  'a remote_mapping * ('a Lwt.t * 'a Lwt.u) =
  let j = r.taskno in
  let m = r.taskmap in
  (* task = cancellable promise *)
  let master, on_master = Lwt.task () in
  let on_worker, worker = Lwt.task () in
  let m = Int.Map.add j { on_master; on_worker } m in
  { r with taskno = j+1; taskmap = m }, (master, worker)
;;

type role = Master | Worker

type event =
 | WorkerStart : 'a remote_mapping * 'state * 'job * ('state -> 'job -> unit Lwt.t) * string -> event
 | WorkerEnd of (int * Unix.process_status)
type 'a events = ([> `DelegationManager of event ] as 'a) Lwt.t list


let pool = Lwt_condition.create ()
let pool_occupants = ref 0
let pool_size = 1 (* TODO: config option *)

let wait_worker pid = [
  Lwt_unix.wait () >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ `DelegationManager (WorkerEnd x)
]

let wait_process proc = [
  proc >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ `DelegationManager (WorkerEnd (0,x))
]

let fork_worker : 'a remote_mapping -> (role * 'b events) Lwt.t = fun remote_mapping ->
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >>= fun () ->
  listen chan 1;
  let address = getsockname chan in
  log @@ "[M] Forking...";
  Lwt_io.flush_all () >>= fun () ->
  let pid = Lwt_unix.fork () in
  if pid = 0 then
    close chan >>= fun () ->
    log @@ "[W] Borning...";
    let chan = socket PF_INET SOCK_STREAM 0 in
    connect chan address >>= fun () ->
    let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
    let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
    let link = { write_to; read_from } in
    new_worker remote_mapping link;
    Lwt.return (Worker, [])
  else
    let timeout = sleep 2. >>= fun () -> Lwt.return None in
    let accept = accept chan >>= fun x -> Lwt.return @@ Some x in
    Lwt.pick [timeout; accept] >>= function
      | None ->
          log @@ "[M] Forked worker does not connect back";
          Lwt.return (Master, []) (* TODO, error *)
      | Some (worker, _worker_addr) -> (* TODO: timeout *)
          close chan >>= fun () ->
          log @@ "[M] Forked pid " ^ string_of_int pid;
          let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
          let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
          let link = { write_to; read_from } in
          new_manager remote_mapping link;
          Lwt.return (Master, wait_worker pid)
;;

let create_process_worker procname state remote_mapping job =
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >>= fun () ->
  listen chan 1;
  let port = match getsockname chan with
    | ADDR_INET(_,port) -> port
    | _ -> assert false in
  let proc =
    (* BIG SUCK: if procname does not exists, this does nothing and
       Lwt.bind waits forever ... *)
    Lwt_process.exec
      (procname,[|procname;"-vscoqtop_master";string_of_int port|]) in
  log @@ "[M] Created worker pid waiting on port " ^ string_of_int port;
  let timeout = sleep 2. >>= fun () -> Lwt.return None in
  let accept = accept chan >>= fun x -> Lwt.return @@ Some x in
  Lwt.pick [timeout; accept] >>= function
  | None -> log @@ "[M] Created worker does not connect back"; Lwt.return [] (* TODO ERR *)
  | Some (worker, _) ->
      close chan >>= fun () ->
      let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
      let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
      let link = { write_to; read_from } in
      new_manager remote_mapping link;
      log @@ "[M] sending mapping";
      Lwt_io.write_value write_to remote_mapping >>= fun () ->
      log @@ "[M] sending state";
      Lwt_io.write_value write_to state >>= fun () ->
      log @@ "[M] sending job";
      Lwt_io.write_value write_to job >>= fun () ->
      Lwt.return (wait_process proc)

let new_process_worker remote_mapping link =
  new_worker remote_mapping link

let handle_event = function
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Lwt.return []
  | WorkerStart (mapping,state,job,action,procname) ->
      if Sys.os_type = "Unix" && false then
        fork_worker mapping >>= fun (role,events) ->
        match role with
        | Master -> Lwt.return events
        | Worker ->
          action state job >>= fun () ->
          log @@ "[W] Worker goes on holidays"; exit 0
      else
        create_process_worker procname state mapping job >>= fun events ->
        Lwt.return events

let worker_available state ~job ~fork_action ~process_action = [
  begin
    if !pool_occupants >= pool_size
    then Lwt_condition.wait pool
    else Lwt.return (incr pool_occupants)
  end
  >>= fun () ->
  job () >>= fun (mapping, job) ->
  Lwt.return @@ `DelegationManager (WorkerStart (mapping,state,job,fork_action,process_action))
]
;;