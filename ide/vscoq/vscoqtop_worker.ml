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

let main_worker options ~opts:_ state =
  let open Lwt.Infix in
  let initial_vernac_state = Vernacstate.freeze_interp_state ~marshallable:false in
  let main () =
    ExecutionManager.WorkerProcess.main ~st:initial_vernac_state options in
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

let islave_default_opts =
  Coqargs.default

let islave_init run_mode ~opts =
  Coqtop.init_toploop opts

let main () =
  let custom = Coqtop.{
      parse_extra = ExecutionManager.WorkerProcess.parse_options;
      help = vscoqtop_specific_usage;
      init = islave_init;
      run = main_worker;
      opts = islave_default_opts } in
  Coqtop.start_coq custom

let _ =
  log @@ "[PW] started";
  Sys.(set_signal sigint Signal_ignore);
  main ()
