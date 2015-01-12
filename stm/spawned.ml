(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Spawn

let pr_err s = Printf.eprintf "(Spawned,%d) %s\n%!" (Unix.getpid ()) s
let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

type chandescr = AnonPipe | Socket of string * int

let handshake cin cout =
  try
    match input_value cin with
    | Hello(v, pid) when v = proto_version ->
        prerr_endline (Printf.sprintf "Handshake with %d OK" pid);
        output_value cout (Hello (proto_version,Unix.getpid ())); flush cout
    | _ -> raise (Failure "handshake protocol")
  with
  | Failure s | Invalid_argument s | Sys_error s ->
      pr_err ("Handshake failed: "  ^ s); raise (Failure "handshake")
  | End_of_file ->
      pr_err "Handshake failed: End_of_file"; raise (Failure "handshake")

let open_bin_connection h p =
  let open Unix in
  let cin, cout = open_connection (ADDR_INET (inet_addr_of_string h,p)) in
  set_binary_mode_in cin true;
  set_binary_mode_out cout true;
  let cin = CThread.prepare_in_channel_for_thread_friendly_io cin in
  cin, cout

let controller h p =
  prerr_endline "starting controller thread";
  let main () =
    let ic, oc = open_bin_connection h p in
    let rec loop () =
      try
        match CThread.thread_friendly_input_value ic with
        | Hello _ -> prerr_endline "internal protocol error"; exit 1
        | ReqDie -> prerr_endline "death sentence received"; exit 0
        | ReqStats ->
            output_value oc (RespStats (Gc.quick_stat ())); flush oc; loop ()
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
  if !channels <> None then Errors.anomaly(Pp.str "init_channels called twice");
  let () = match !main_channel with
  | None -> ()
  | Some (Socket(mh,mp)) ->
    channels := Some (open_bin_connection mh mp);
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
  | Some (Socket (ch, cp)) ->
    controller ch cp
  | Some AnonPipe ->
    Errors.anomaly (Pp.str "control channel cannot be a pipe")

let get_channels () =
  match !channels with
  | None -> Errors.anomaly(Pp.str "init_channels not called")
  | Some(ic, oc) -> ic, oc

