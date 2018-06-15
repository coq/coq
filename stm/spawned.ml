(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Spawn

let pr_err s = Printf.eprintf "(Spawned,%d) %s\n%!" (Unix.getpid ()) s
let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

type chandescr = AnonPipe | Socket of string * int * int

let open_bin_connection h pr pw =
  let open Unix in
  let _, cout = open_connection (ADDR_INET (inet_addr_of_string h,pr)) in
  let cin, _ = open_connection (ADDR_INET (inet_addr_of_string h,pw)) in
  set_binary_mode_in cin true;
  set_binary_mode_out cout true;
  let cin = CThread.prepare_in_channel_for_thread_friendly_io cin in
  cin, cout

let controller h pr pw =
  prerr_endline "starting controller thread";
  let main () =
    let ic, oc = open_bin_connection h pr pw in
    let loop () =
      try
        match CThread.thread_friendly_input_value ic with
        | Hello _ -> prerr_endline "internal protocol error"; exit 1
        | ReqDie -> prerr_endline "death sentence received"; exit 0
      with
      | e ->
        prerr_endline ("control channel broken: " ^ Printexc.to_string e);
        exit 1 in
    loop () in
  ignore(Thread.create main ())

let main_channel = ref None
let control_channel = ref None

let channels = ref None

let init_channels () =
  if !channels <> None then CErrors.anomaly(Pp.str "init_channels called twice.");
  let () = match !main_channel with
  | None -> ()
  | Some (Socket(mh,mpr,mpw)) ->
    channels := Some (open_bin_connection mh mpr mpw);
  | Some AnonPipe ->
    let stdin = Unix.in_channel_of_descr (Unix.dup Unix.stdin) in
    let stdout = Unix.out_channel_of_descr (Unix.dup Unix.stdout) in
    Unix.dup2 Unix.stderr Unix.stdout;
    set_binary_mode_in stdin true;
    set_binary_mode_out stdout true;
    let stdin = CThread.prepare_in_channel_for_thread_friendly_io stdin in
    channels := Some (stdin, stdout);
  in
  match !control_channel with
  | None -> ()
  | Some (Socket (ch, cpr, cpw)) ->
    controller ch cpr cpw
  | Some AnonPipe ->
    CErrors.anomaly (Pp.str "control channel cannot be a pipe.")

let get_channels () =
  match !channels with
  | None ->
    Printf.eprintf "Fatal error: ideslave communication channels not set.\n";
    exit 1
  | Some(ic, oc) -> ic, oc

let process_id () =
  Printf.sprintf "%d:%s:%d" (Unix.getpid ())
    (if Flags.async_proofs_is_worker () then !Flags.async_proofs_worker_id
     else "master")
    (Thread.id (Thread.self ()))
