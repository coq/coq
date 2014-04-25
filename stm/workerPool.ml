(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Make(Worker : sig
  type process
  val spawn :
      ?prefer_sock:bool -> ?env:string array -> string -> string array ->
      process * in_channel * out_channel
end) = struct

type worker_id = int
type spawn =
  args:string array -> env:string array -> unit ->
    in_channel * out_channel * Worker.process

let slave_managers = ref None

let n_workers () = match !slave_managers with
  | None -> 0
  | Some managers -> Array.length managers
let is_empty () = !slave_managers = None

let magic_no = 17

let master_handshake worker_id ic oc =
  try
    Marshal.to_channel oc magic_no [];  flush oc;
    let n = (Marshal.from_channel ic : int) in
    if n <> magic_no then begin
      Printf.eprintf "Handshake with %d failed: protocol mismatch\n" worker_id;
      exit 1;
    end
  with e when Errors.noncritical e ->
    Printf.eprintf "Handshake with %d failed: %s\n"
      worker_id (Printexc.to_string e);
    exit 1

let respawn n ~args ~env () =
  let proc, ic, oc = Worker.spawn ~env Sys.argv.(0) args in
  master_handshake n ic oc;
  ic, oc, proc

let init ~size:n ~manager:manage_slave =
  slave_managers := Some
    (Array.init n (fun x ->
       let cancel = ref false in
       cancel, Thread.create (manage_slave ~cancel (x+1)) (respawn (x+1))))

let cancel n =
  match !slave_managers with
  | None -> ()
  | Some a ->
      let switch, _ = a.(n) in
      switch := true
      
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

end
