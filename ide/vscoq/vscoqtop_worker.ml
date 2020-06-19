(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This toplevel implements an LSP-based server language for VsCode,
    used by the VsCoq extension. *)

let log msg = Format.eprintf "%d] @[%s@]@\n%!" (Unix.getpid ()) msg

let main_worker port ~opts:_ state =
  let open Lwt.Infix in
  let open Lwt_unix in
  let main () =
    let chan = socket PF_INET SOCK_STREAM 0 in
    let address = ADDR_INET (Unix.inet_addr_loopback,port) in
    log @@ "[PW] connecting to " ^ string_of_int port;
    connect chan address >>= fun () ->
    let read_from = Lwt_io.of_fd ~mode:Lwt_io.Input chan in
    let write_to = Lwt_io.of_fd ~mode:Lwt_io.Output chan in
    let link = { DelegationManager.read_from; write_to } in
    Lwt_io.read_value read_from >>= fun mapping ->
    Lwt_io.read_value read_from >>= fun state ->
    Lwt_io.read_value read_from >>= fun job ->
    let state = ExecutionManager.new_process_worker state mapping link in
    ExecutionManager.worker_main state job in
  try Lwt_main.run @@ main ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    log Printexc.(to_string exn);
    log bt;
    flush_all ()

let vscoqtop_specific_usage = Usage.{
  executable_name = "vscoqtop";
  extra_args = "";
  extra_options = "";
}

let islave_parse ~opts extra_args =
  match extra_args with
  [ "-vscoqtop_master"; port ] -> int_of_string port, []
  | _ -> assert false

let islave_default_opts =
  Coqargs.default

let islave_init run_mode ~opts =
  Coqtop.init_toploop opts

let main () =
  let custom = Coqtop.{
      parse_extra = islave_parse;
      help = vscoqtop_specific_usage;
      init = islave_init;
      run = main_worker;
      opts = islave_default_opts } in
  Coqtop.start_coq custom

let _ =
  log @@ "[PW] started";
  Sys.(set_signal sigint Signal_ignore);
  main ()
