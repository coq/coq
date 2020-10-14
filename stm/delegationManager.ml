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
open Lwt_err.Infix

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

type sentence_id = Stateid.t
type ('a,'b) coqtop_extra_args_fn = opts:'b -> string list -> 'a * string list

type link = {
  write_to :  Lwt_io.output_channel;
  read_from:  Lwt_io.input_channel;
  pid : int option;
}

let kill_link { pid } () = match pid with
  | Some pid -> Unix.kill pid 9
  | None -> ()

type ('a,'b) corresponding = { on_worker : 'b; on_master : 'a; cancel : 'b }

module M = Map.Make(Stateid)
type 'a remote_mapping = {
  it : ('a Lwt.u, 'a Lwt.t) corresponding M.t;
  progress_hook : unit -> unit Lwt.t
}


module type Job = sig
  type t
  val name : string
  val binary_name : string
  val pool_size : int
end

module Make (Job : Job) = struct

let option_name = "-" ^ Str.global_replace (Str.regexp_string " ") "." Job.name ^ "_master_address"


let marshalable_remote_mapping { it } = M.bindings it |> List.map (fun (id,_) -> id)

let empty_remote_mapping ~progress_hook = {
  it = M.empty;
  progress_hook;
}

type event =
 | WorkerStart : 'a remote_mapping * 'job * ('job -> unit Lwt.t) * string -> event
 | WorkerDied
 | WorkerProgress : link * 'a remote_mapping -> event
 | WorkerEnd of (int * Unix.process_status)
type events = event Lwt.t list

let worker_progress link remote_mapping =
  Lwt_io.read_value link.read_from >?= function
    | Result.Error e ->
      log @@ "[M] Worker died: " ^ Printexc.to_string e;
      Lwt.return WorkerDied
    | Result.Ok (i,v) ->
      let resolver = M.find i remote_mapping.it in
      log @@ "[M] Manager fulfilling " ^ Stateid.to_string i;
      Lwt.wakeup_later resolver.on_master v;
      Lwt.return @@ WorkerProgress(link,remote_mapping)

(* Reads values from the worker and passes them to the resolvers in master *)
let trap_cancel : 'a remote_mapping -> link -> unit = fun remote_mapping link ->
  log @@ "[M] installing cancel trap";
    M.iter (fun _ { cancel } -> Lwt.on_cancel cancel (kill_link link)) remote_mapping.it

(* Reads values from the local premises and writes them to master *)
let new_worker : 'a remote_mapping -> link -> unit = fun remote_mapping link ->
  let m = Lwt_mutex.create () in
  log @@ "[W] installing async fulfillers";
  Lwt.async_exception_hook := (fun x ->
    log @@ "[W] Worker terminated " ^ Printexc.to_string x); (* HACK *)
  M.iter (fun i { on_worker } ->
    Lwt.async @@ (fun () -> on_worker >>= fun v ->
      Lwt_mutex.with_lock m (fun () -> (* Mutex maybe not needed *)
        log @@ "[W] Remote fulfilling of " ^ Stateid.to_string i;
        Lwt_io.write_value link.write_to (i,v) >!= fun () ->
        Lwt_io.flush_all ())
    )
  ) remote_mapping.it
;;

(* Like Lwt.wait but the resolved is remote_mapping, via IPC *)
let lwt_remotely_wait r id =
  let m = r.it in
  (* task = cancellable promise *)
  let master, on_master = Lwt.task () in
  let on_worker, worker = Lwt.task () in
  let m = M.add id { on_master; on_worker; cancel = master } m in
  { r with it = m }, (master, worker)
;;

type role = Master | Worker

let pool = Lwt_condition.create ()
let pool_occupants = ref 0
let pool_size = Job.pool_size

let wait_worker pid =
  Lwt_unix.wait () >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ WorkerEnd x

let wait_process proc =
  proc#close >>= fun x ->
  decr pool_occupants; Lwt_condition.signal pool ();
  log @@ "[T] vacation request ready";
  Lwt.return @@ WorkerEnd (0,x)

let fork_worker : 'a remote_mapping -> (role * events) Lwt.t = fun remote_mapping ->
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >>= fun () ->
  listen chan 1;
  let address = getsockname chan in
  log @@ "[M] Forking...";
  Lwt_io.flush_all () >!= fun () ->
  let pid = Lwt_unix.fork () in
  if pid = 0 then
    close chan >>= fun () ->
    log @@ "[W] Borning...";
    let chan = socket PF_INET SOCK_STREAM 0 in
    connect chan address >>= fun () ->
    let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
    let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
    let link = { write_to; read_from; pid = None } in
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
          close chan >!= fun () ->
          log @@ "[M] Forked pid " ^ string_of_int pid;
          let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
          let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
          let link = { write_to; read_from; pid = Some pid } in
          trap_cancel remote_mapping link;
          Lwt.return (Master, [worker_progress link remote_mapping; wait_worker pid])
;;

let create_process_worker procname remote_mapping job =
  let open Lwt_unix in
  let chan = socket PF_INET SOCK_STREAM 0 in
  bind chan (ADDR_INET (Unix.inet_addr_loopback,0)) >!= fun () ->
  listen chan 1;
  let port = match getsockname chan with
    | ADDR_INET(_,port) -> port
    | _ -> assert false in
  let proc =
    new Lwt_process.process_none
      (procname,[|procname;option_name;string_of_int port|]) in
  log @@ "[M] Created worker pid waiting on port " ^ string_of_int port;
  let timeout = sleep 2. >>= fun () -> Lwt.return None in
  let accept = accept chan >>= fun x -> Lwt.return @@ Some x in
  Lwt.pick [timeout; accept] >>= function
  | None -> log @@ "[M] Created worker does not connect back"; Lwt.return [] (* TODO ERR *)
  | Some (worker, _) ->
      close chan >>= fun () ->
      let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input worker in
      let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output worker in
      let link = { write_to; read_from; pid = Some proc#pid } in
      trap_cancel remote_mapping link;
      log @@ "[M] sending mapping";
      Lwt_io.write_value write_to (marshalable_remote_mapping remote_mapping) >!= fun () ->
      log @@ "[M] sending job";
      Lwt_io.write_value write_to job >!= fun () ->
      Lwt.return [worker_progress link remote_mapping; wait_process proc]

let new_process_worker remote_mapping link =
  new_worker remote_mapping link

let handle_event = function
  | WorkerEnd (pid, _status) ->
      log @@ Printf.sprintf "[M] Worker %d went on holidays" pid;
      Lwt.return []
  | WorkerDied ->
      log @@ Printf.sprintf "[M] Worker died";
      Lwt.return []
  | WorkerProgress (link,remote_mapping) ->
    Lwt.return [worker_progress link remote_mapping]
  | WorkerStart (mapping,job,action,procname) ->
      if Sys.os_type = "Unix" then
        fork_worker mapping >>= fun (role,events) ->
        match role with
        | Master -> Lwt.return events
        | Worker ->
          action job >>= fun () ->
          log @@ "[W] Worker goes on holidays"; exit 0
      else
        create_process_worker procname mapping job

let worker_available ~job ~fork_action = [
  begin
    if !pool_occupants >= pool_size
    then Lwt_condition.wait pool
    else Lwt.return (incr pool_occupants)
  end
  >>= fun () ->
  job () >>= fun (mapping, job) ->
  Lwt.return @@ WorkerStart (mapping,job,fork_action,Job.binary_name)
]
;;

type options = int

let setup_plumbing port =
  let open Lwt_unix in
  (* TODO: encalpsulate this into a function in DelegationManager *)
  let chan = socket PF_INET SOCK_STREAM 0 in
  let address = ADDR_INET (Unix.inet_addr_loopback,port) in
  log @@ "[PW] connecting to " ^ string_of_int port;
  connect chan address >!= fun () ->
  let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
  let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
  let link = { read_from; write_to; pid = None } in
  Lwt_io.read_value link.read_from >!= fun (ids : sentence_id list) ->
  Lwt_io.read_value link.read_from >!= fun (job : Job.t) ->
  Lwt.return (ids, link, job)

let parse_options ~opts extra_args =
  match extra_args with
  [ o ; port ] when o = option_name -> int_of_string port, []
  | _ -> assert false (* TODO: error *)

end
