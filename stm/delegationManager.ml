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
 | WorkerStart : 'a remote_mapping * 'job * ('job -> unit Lwt.t) -> event
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

let handle_event = function
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Lwt.return []
  | WorkerStart (mapping,job,action) ->
      fork_worker mapping >>= fun (role,events) ->
      match role with
      | Master -> Lwt.return events
      | Worker ->
         action job >>= fun () ->
         log @@ "[W] Worker goes on holidays"; exit 0

let worker_available ~job ~action = [
  begin
    if !pool_occupants >= pool_size
    then Lwt_condition.wait pool
    else Lwt.return (incr pool_occupants)
  end
  >>= fun () ->
  job () >>= fun (mapping, job) ->
  Lwt.return @@ `DelegationManager (WorkerStart (mapping,job,action))
]
;;