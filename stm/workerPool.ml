(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type worker_id = string

type 'a cpanel = {
  exit : unit -> unit; (* called by manager to exit instead of Thread.exit *)
  cancelled : unit -> bool; (* manager checks for a request of termination *)
  extra : 'a;                        (* extra stuff to pass to the manager *)
}

module type PoolModel = sig
  (* this shall come from a Spawn.* model *)
  type process
  val spawn : int -> worker_id * process * CThread.thread_ic * out_channel

  (* this defines the main loop of the manager *)
  type extra
  val manager :
    extra cpanel -> worker_id * process * CThread.thread_ic * out_channel -> unit
end

module Make(Model : PoolModel) = struct

type worker = {
  name : worker_id;
  cancel : bool ref;
  manager : Thread.t;
  process : Model.process;
}

type pre_pool = {
  workers : worker list ref;
  count : int ref;
  extra_arg : Model.extra;
}

type pool = { lock : Mutex.t; pool : pre_pool }

let magic_no = 17

let master_handshake worker_id ic oc =
  try
    Marshal.to_channel oc magic_no [];  flush oc;
    let n = (CThread.thread_friendly_input_value ic : int) in
    if n <> magic_no then begin
      Printf.eprintf "Handshake with %s failed: protocol mismatch\n" worker_id;
      exit 1;
    end
  with e when CErrors.noncritical e ->
    Printf.eprintf "Handshake with %s failed: %s\n"
      worker_id (Printexc.to_string e);
    exit 1

let worker_handshake slave_ic slave_oc =
  try
    let v = (CThread.thread_friendly_input_value slave_ic : int) in
    if v <> magic_no then begin
      prerr_endline "Handshake failed: protocol mismatch\n";
      exit 1;
    end;
    Marshal.to_channel slave_oc v []; flush slave_oc;
  with e when CErrors.noncritical e ->
    prerr_endline ("Handshake failed: " ^ Printexc.to_string e);
    exit 1

let locking { lock; pool = p } f =
  try
    Mutex.lock lock;
    let x = f p in
    Mutex.unlock lock;
    x
  with e -> Mutex.unlock lock; raise e

let rec create_worker extra pool id =
  let cancel = ref false in
  let name, process, ic, oc as worker = Model.spawn id in
  master_handshake name ic oc;
  let exit () = cancel := true; cleanup pool; Thread.exit () in
  let cancelled () = !cancel in
  let cpanel = { exit; cancelled; extra } in
  let manager = Thread.create (Model.manager cpanel) worker in
  { name; cancel; manager; process }
  
and cleanup x = locking x begin fun { workers; count; extra_arg } ->
  workers := List.map (function
    | { cancel } as w when !cancel = false -> w
    | _ -> let n = !count in incr count; create_worker extra_arg x n)
  !workers
end

let n_workers x = locking x begin fun { workers } ->
   List.length !workers
end

let is_empty x = locking x begin fun { workers } -> !workers = [] end

let create extra_arg ~size = let x = {
    lock = Mutex.create ();
    pool = {
      extra_arg;
      workers = ref [];
      count = ref size;
  }} in
  locking x begin fun { workers } ->
     workers := CList.init size (create_worker extra_arg x)
  end;
  x

let cancel n x = locking x begin fun { workers } ->
  List.iter (fun { name; cancel } -> if n = name then cancel := true) !workers
end

let cancel_all x = locking x begin fun { workers } ->
  List.iter (fun { cancel } -> cancel := true) !workers
end

let destroy x = locking x begin fun { workers } ->
  List.iter (fun { cancel } -> cancel := true) !workers;
  workers := []
end

end
