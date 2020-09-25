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

let loop run_mode ~opts:_ state =
  LspManager.init ();
  let _feeder_id = Feedback.add_feeder LspManager.handle_feedback in
  let open Lwt.Infix in
  let rec loop (events : LspManager.events) =
    log @@ "[T] looking for next step";
    Lwt_io.flush_all () >>= fun () ->
    Lwt.nchoose_split events >>= fun (ready, remaining) ->
      let perform acc e =
          LspManager.handle_event e >>= fun more_events ->
          Lwt.return @@ acc @ more_events
     in
        Lwt_list.fold_left_s perform remaining ready >>= fun events ->
        loop events
  in
  try Lwt_main.run @@ loop (LspManager.lsp ())
  with exn ->
    let bt = Printexc.get_backtrace () in
    log Printexc.(to_string exn);
    log bt;
    flush_all ()

let vscoqtop_specific_usage = {
  Usage.executable_name = "vscoqtop";
  extra_args = "";
  extra_options = "";
}

let islave_parse ~opts extra_args =
  let open Coqtop in
  let run_mode, extra_args = coqtop_toplevel.parse_extra ~opts extra_args in
  run_mode, []

let islave_default_opts =
  Coqargs.{ default with
    config = { default.config with
      stm_flags = { default.config.stm_flags with
         Stm.AsyncOpts.async_proofs_worker_priority = CoqworkmgrApi.High }}}

let islave_init run_mode ~opts =
  Coqtop.init_toploop opts

let main () =
  let custom = Coqtop.{
      parse_extra = islave_parse;
      help = vscoqtop_specific_usage;
      init = islave_init;
      run = loop;
      opts = islave_default_opts } in
  Coqtop.start_coq custom

let _ =
  Sys.(set_signal sigint Signal_ignore);
  main ()
