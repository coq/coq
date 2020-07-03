(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs

(** This file provides generic support for Coq executables + specific
    support for the coqtop executable *)

let () = at_exit flush_all

let ( / ) = Filename.concat

let get_version_date () =
  try
    let ch = open_in (Envars.coqlib () / "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    (ver,rev)
  with e when CErrors.noncritical e ->
    (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = get_version_date () in
  Feedback.msg_info (str "Welcome to Coq " ++ str ver ++ str " (" ++ str rev ++ str ")");
  flush_all ()

let print_memory_stat () =
  (* -m|--memory from the command-line *)
  Feedback.msg_notice
    (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ());
  (* operf-macro interface:
     https://github.com/OCamlPro/operf-macro *)
  try
    let fn = Sys.getenv "OCAML_GC_STATS" in
    let oc = open_out fn in
    Gc.print_stat oc;
    close_out oc
  with _ -> ()

(******************************************************************************)
(* Input/Output State                                                         *)
(******************************************************************************)
let inputstate opts =
  Option.iter (fun istate_file ->
    let fname = Loadpath.locate_file (CUnix.make_suffix istate_file ".coq") in
    Library.intern_state fname) opts.inputstate

(******************************************************************************)
(* Fatal Errors                                                               *)
(******************************************************************************)

(** Prints info which is either an error or an anomaly and then exits
    with the appropriate error code *)
let fatal_error_exn exn =
  Topfmt.(in_phase ~phase:Initialization print_err_exn exn);
  flush_all ();
  let exit_code =
    if (CErrors.is_anomaly exn) then 129 else 1
  in
  exit exit_code

(******************************************************************************)
(* Color Options                                                              *)
(******************************************************************************)
let init_color opts =
  let has_color = match opts.color with
  | `OFF -> false
  | `EMACS -> false
  | `ON -> true
  | `AUTO ->
    Terminal.has_style Unix.stdout &&
    Terminal.has_style Unix.stderr &&
    (* emacs compilation buffer does not support colors by default,
       its TERM variable is set to "dumb". *)
    try Sys.getenv "TERM" <> "dumb" with Not_found -> false
  in
  let term_color =
    if has_color then begin
      let colors = try Some (Sys.getenv "COQ_COLORS") with Not_found -> None in
      match colors with
      | None -> Topfmt.default_styles (); true        (* Default colors *)
      | Some "" -> false                              (* No color output *)
      | Some s -> Topfmt.parse_color_config s; true   (* Overwrite all colors *)
    end
    else begin
      Topfmt.default_styles (); false                 (* textual markers, no color *)
    end
  in
  if opts.color = `EMACS then
    Topfmt.set_emacs_print_strings ()
  else if not term_color then begin
      Proof_diffs.write_color_enabled term_color;
    if Proof_diffs.show_diffs () then
      (prerr_endline "Error: -diffs requires enabling -color"; exit 1)
  end;
  Topfmt.init_terminal_output ~color:term_color

let print_style_tags opts =
  let () = init_color opts in
  let tags = Topfmt.dump_tags () in
  let iter (t, st) =
    let opt = Terminal.eval st ^ t ^ Terminal.reset ^ "\n" in
    print_string opt
  in
  let make (t, st) =
    let tags = List.map string_of_int (Terminal.repr st) in
    (t ^ "=" ^ String.concat ";" tags)
  in
  let repr = List.map make tags in
  let () = Printf.printf "COQ_COLORS=\"%s\"\n" (String.concat ":" repr) in
  let () = List.iter iter tags in
  flush_all ()

let init_coqlib opts = match opts.config.coqlib with
  | None when opts.pre.boot -> ()
  | None ->
    Envars.set_coqlib ~fail:(fun msg -> CErrors.user_err Pp.(str msg));
  | Some s ->
    Envars.set_user_coqlib s

let print_query opts = function
  | PrintVersion -> Usage.version ()
  | PrintMachineReadableVersion -> Usage.machine_readable_version ()
  | PrintWhere ->
    let () = init_coqlib opts in
    print_endline (Envars.coqlib ())
  | PrintHelp h -> Usage.print_usage stderr h
  | PrintConfig ->
    let () = init_coqlib opts in
    Envars.print_config stdout Coq_config.all_src_dirs
  | PrintTags -> print_style_tags opts.config

(** GC tweaking *)

(** Coq is a heavy user of persistent data structures and symbolic ASTs, so the
    minor heap is heavily solicited. Unfortunately, the default size is far too
    small, so we enlarge it a lot (128 times larger).

    To better handle huge memory consumers, we also augment the default major
    heap increment and the GC pressure coefficient.
*)

let init_gc () =
  try
    (* OCAMLRUNPARAM environment variable is set.
     * In that case, we let ocamlrun to use the values provided by the user.
     *)
    ignore (Sys.getenv "OCAMLRUNPARAM")

  with Not_found ->
    (* OCAMLRUNPARAM environment variable is not set.
     * In this case, we put in place our preferred configuration.
     *)
    Gc.set { (Gc.get ()) with
             Gc.minor_heap_size = 32*1024*1024; (* 32Mwords x 8 bytes/word = 256Mb *)
             Gc.space_overhead = 120}

let init_process () =
  (* Coq's init process, phase 1:
     OCaml parameters, basic structures, and IO
   *)
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init ()

let init_parse parse_extra help init_opts =
  let opts, extras =
    parse_args ~help:help ~init:init_opts
      (List.tl (Array.to_list Sys.argv)) in
  let customopts, extras = parse_extra ~opts extras in
  if not (CList.is_empty extras) then begin
    prerr_endline ("Don't know what to do with "^String.concat " " extras);
    prerr_endline "See -help for the list of supported options";
    exit 1
    end;
  opts, customopts

(** Coq's init process, phase 2: Basic Coq environment, plugins. *)
let init_execution opts custom_init =
  (* If we have been spawned by the Spawn module, this has to be done
   * early since the master waits us to connect back *)
  Spawned.init_channels ();
  if opts.post.memory_stat then at_exit print_memory_stat;
  CoqworkmgrApi.(init opts.config.stm_flags.Stm.AsyncOpts.async_proofs_worker_priority);
  Mltop.init_known_plugins ();
  (* Configuration *)
  Global.set_engagement opts.config.logic.impredicative_set;
  Global.set_indices_matter opts.config.logic.indices_matter;
  Global.set_VM opts.config.enable_VM;
  Flags.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);
  Global.set_native_compiler (match opts.config.native_compiler with NativeOff -> false | NativeOn _ -> true);

  (* Native output dir *)
  Nativelib.output_dir := opts.config.native_output_dir;
  Nativelib.include_dirs := opts.config.native_include_dirs;

  (* Allow the user to load an arbitrary state here *)
  inputstate opts.pre;

  (* This state will be shared by all the documents *)
  Stm.init_core ();
  custom_init ~opts

type 'a extra_args_fn = opts:Coqargs.t -> string list -> 'a * string list

type ('a,'b) custom_toplevel =
  { parse_extra : 'a extra_args_fn
  ; help : Usage.specific_usage
  ; init : 'a -> opts:Coqargs.t -> 'b
  ; run : 'a -> opts:Coqargs.t -> 'b -> unit
  ; opts : Coqargs.t
  }

(** Main init routine *)
let init_toplevel custom =
  let () = init_process () in
  let opts, customopts = init_parse custom.parse_extra custom.help custom.opts in
  (* Querying or running? *)
  match opts.main with
  | Queries q -> List.iter (print_query opts) q; exit 0
  | Run ->
    let () = init_coqlib opts in
    let customstate = init_execution opts (custom.init customopts) in
    opts, customopts, customstate

let init_document opts =
  (* Coq init process, phase 3: Stm initialization, backtracking state.

     It is essential that the module system is in a consistent
     state before we take the first snapshot. This was not
     guaranteed in the past, but now is thanks to the STM API.
  *)
  (* Next line allows loading .vos files when in interactive mode *)
  Flags.load_vos_libraries := true;
  let ml_load_path, vo_load_path = build_load_path opts in
  let injections = injection_commands opts in
  let stm_options = opts.config.stm_flags in
  let open Vernac.State in
  let doc, sid =
    Stm.(new_doc
           { doc_type = Interactive opts.config.logic.toplevel_name;
             ml_load_path; vo_load_path; injections; stm_options;
           }) in
  { doc; sid; proof = None; time = opts.config.time }

let start_coq custom =
  let init_feeder = Feedback.add_feeder Coqloop.coqloop_feed in
  (* Init phase *)
  let opts, custom_opts, state =
    try init_toplevel custom
    with any ->
      flush_all();
      fatal_error_exn any in
  Feedback.del_feeder init_feeder;
  (* Run phase *)
  custom.run ~opts custom_opts state

(** ****************************************)
(** Specific support for coqtop executable *)

type run_mode = Interactive | Batch

let init_toploop opts =
  let state = init_document opts in
  let state = Ccompile.load_init_vernaculars opts ~state in
  state

let coqtop_init run_mode ~opts =
  if run_mode = Batch then Flags.quiet := true;
  init_color opts.config;
  Flags.if_verbose print_header ();
  init_toploop opts

let coqtop_parse_extra ~opts extras =
  let rec parse_extra run_mode = function
  | "-batch" :: rest -> parse_extra Batch rest
  | x :: rest ->
    let run_mode, rest = parse_extra run_mode rest in run_mode, x :: rest
  | [] -> run_mode, [] in
  let run_mode, extras = parse_extra Interactive extras in
  run_mode, extras

let coqtop_run run_mode ~opts state =
  match run_mode with
  | Interactive -> Coqloop.loop ~opts ~state;
  | Batch -> exit 0

let coqtop_specific_usage = Usage.{
  executable_name = "coqtop";
  extra_args = "";
  extra_options = "\n\
coqtop specific options:\n\
\n  -batch                 batch mode (exits after interpretation of command line)\
\n"
}

let coqtop_toplevel =
  { parse_extra = coqtop_parse_extra
  ; help = coqtop_specific_usage
  ; init = coqtop_init
  ; run = coqtop_run
  ; opts = Coqargs.default
  }
