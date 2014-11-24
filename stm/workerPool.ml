(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type worker_id = string
type 'a spawn =
  args:string array -> env:string array -> unit -> in_channel * out_channel * 'a
type active
type parking

module type WorkerModel = sig
  type process
  val spawn :
    ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      process * in_channel * out_channel
end

module type ManagerModel = sig
  type process
  type extra (* extra stuff to pass to the manager *)
  val manager :
    extra -> cancel:bool ref -> die:bool ref -> worker_id -> process spawn ->
      unit
  val naming : int -> worker_id
end


module Make(Worker : WorkerModel)
           (Manager : ManagerModel with type process = Worker.process) = struct

type worker = {
  name : worker_id;
  cancel : bool ref;
  die : bool ref;
  manager : Thread.t }

type 'a pool = {
  workers : worker list ref;
  count : int ref;
  extra : Manager.extra option;
  lock : Mutex.t
}

let n_workers { workers } = List.length !workers
let is_empty { workers } = !workers = []

let magic_no = 17

let master_handshake worker_id ic oc =
  try
    Marshal.to_channel oc magic_no [];  flush oc;
    let n = (Marshal.from_channel ic : int) in
    if n <> magic_no then begin
      Printf.eprintf "Handshake with %s failed: protocol mismatch\n" worker_id;
      exit 1;
    end
  with e when Errors.noncritical e ->
    Printf.eprintf "Handshake with %s failed: %s\n"
      worker_id (Printexc.to_string e);
    exit 1

let worker_handshake slave_ic slave_oc =
  try
    let v = (Marshal.from_channel slave_ic : int) in
    if v <> magic_no then begin
      prerr_endline "Handshake failed: protocol mismatch\n";
      exit 1;
    end;
    Marshal.to_channel slave_oc v []; flush slave_oc;
  with e when Errors.noncritical e ->
    prerr_endline ("Handshake failed: " ^ Printexc.to_string e);
    exit 1

let respawn n ~args ~env () =
  let proc, ic, oc = Worker.spawn ~env Sys.argv.(0) args in
  master_handshake n ic oc;
  ic, oc, proc

let create1 e x =
  let name = Manager.naming x in
  let cancel = ref false in
  let die = ref false in
  let manager =
    Thread.create (Manager.manager e ~cancel ~die name) (respawn name) in
  { name; cancel; die; manager }

let create_active e n = {
  lock = Mutex.create ();
  extra = Some e;
  workers = ref (CList.init n (create1 e));
  count = ref n
}

let create_parking () = {
  lock = Mutex.create ();
  extra = None;
  workers = ref [];
  count = ref 0
}

let cancel { lock; workers } n =
  Mutex.lock lock;
  List.iter (fun { name; cancel } -> if n = name then cancel := true) !workers;
  Mutex.unlock lock

let cancel_all { lock; workers } =
  Mutex.lock lock;
  List.iter (fun { cancel } -> cancel := true) !workers;
  Mutex.unlock lock

let kill_all { lock; workers } =
  Mutex.lock lock;
  List.iter (fun { die } -> die := true) !workers;
  Mutex.unlock lock

let destroy { lock; workers } =
  Mutex.lock lock;
  List.iter (fun { die } -> die := true) !workers;
  workers := [];
  Mutex.unlock lock

let move oldq newq n =
  Mutex.lock oldq.lock; Mutex.lock newq.lock;
  let rec find acc = function
    | [] -> Mutex.unlock oldq.lock; Mutex.unlock newq.lock; assert false
    | { name } as w :: rest when name = n -> w, List.rev acc @ rest
    | x :: xs -> find (x :: acc) xs in
  let w, rest = find [] !(oldq.workers) in
  oldq.workers := create1 (Option.get oldq.extra) !(oldq.count) :: rest;
  oldq.count := !(oldq.count) + 1;
  newq.workers := w :: !(newq.workers);
  Mutex.unlock oldq.lock; Mutex.unlock newq.lock

end
