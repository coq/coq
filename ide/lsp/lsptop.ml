(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr
open Vernacprop
open CErrors
open Util
open Pp
open Printer

let init_signal_handler () =
  let f _ = Control.interrupt := true in
  Sys.set_signal Sys.sigint (Sys.Signal_handle f)

let pr_with_pid s = Printf.eprintf "[pid %d] %s\n%!" (Unix.getpid ()) s
let pr_error s = pr_with_pid s

let ide_doc = ref None
let get_doc () = Option.get !ide_doc
let set_doc doc = ide_doc := Some doc

let quit = ref (-1)

(** The main loop *)
let loop ( { Coqtop.run_mode; color_mode },_) ~opts:_ state =
  match run_mode with
  | Coqtop.Batch -> exit 0
  | Coqtop.(Query PrintTags) -> Coqtop.print_style_tags color_mode; exit 0
  | Coqtop.(Query _) -> Printf.eprintf "Unknown query"; exit 1
  | Coqtop.Interactive ->
  let open Vernac.State in
  set_doc state.doc;
  init_signal_handler ();
  let in_ch, out_ch = Spawned.get_channels () in
  let json_oc       = out_ch in
  (* TODO! *)
  let json_ic       = Stream.from (fun s len ->
                      CThread.thread_friendly_read in_ch s ~off:0 ~len) in
  let process_json json_ic json_oc out_ch =
    let open Yojson.Basic in
    let open Lsp in
    let open Json_helper in
    let lsp_query = read_lsp_query json_ic in
      match run_query state lsp_query.q with
      | (Some r, State _) -> to_channel json_oc (lsp_of_response lsp_query.query_id r)
      | (None, _) -> quit := 1
      | (_, ExitCode c) -> quit := c;
    flush out_ch
  in

  while !quit < 0 do
    process_json json_ic json_oc out_ch
  done;
  exit !quit

let islave_parse extra_args =
  let open Coqtop in
  let ({ run_mode; color_mode }, stm_opts), extra_args = coqtop_toplevel.parse_extra extra_args in
  let extra_args = parse extra_args in
  (* One of the role of coqidetop is to find the name of buffers to open *)
  (* in the command line; Coqide is waiting these names on stdout *)
  (* (see filter_coq_opts in coq.ml), so we send them now *)
  print_string (String.concat "\n" extra_args);
  ( { Coqtop.run_mode; color_mode }, stm_opts), []

let islave_init ( { Coqtop.run_mode; color_mode }, stm_opts) injections ~opts =
  if run_mode = Coqtop.Batch then Flags.quiet := true;
  Coqtop.init_toploop opts stm_opts injections

let islave_default_opts = Coqargs.default

let islave_usage = Boot.Usage.{
  executable_name = "coqlsptop";
  extra_args = "";
  extra_options = "";
}

let islave_parse extra_args =
  let open Coqtop in
  let ({ run_mode; color_mode }, stm_opts), extra_args = coqtop_toplevel.parse_extra extra_args in
  let extra_args = parse extra_args in
  (* One of the role of coqidetop is to find the name of buffers to open *)
  (* in the command line; Coqide is waiting these names on stdout *)
  (* (see filter_coq_opts in coq.ml), so we send them now *)
  print_string (String.concat "\n" extra_args);
  ( { Coqtop.run_mode; color_mode }, stm_opts), []


let () =
  let open Coqtop in
  let custom = {
      usage = islave_usage;
      parse_extra = islave_parse;
      init_extra = islave_init;
      run = loop;
      initial_args = islave_default_opts } in
  start_coq custom
