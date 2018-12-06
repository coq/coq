(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Coqargs

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
  Feedback.msg_notice (str "Welcome to Coq " ++ str ver ++ str " (" ++ str rev ++ str ")");
  flush_all ()

let memory_stat = ref false
let print_memory_stat () =
  begin (* -m|--memory from the command-line *)
    if !memory_stat then
    Feedback.msg_notice
      (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ());
  end;
  begin
    (* operf-macro interface:
       https://github.com/OCamlPro/operf-macro *)
    try
      let fn = Sys.getenv "OCAML_GC_STATS" in
      let oc = open_out fn in
      Gc.print_stat oc;
      close_out oc
    with _ -> ()
  end

let _ = at_exit print_memory_stat

(******************************************************************************)
(* Input/Output State                                                         *)
(******************************************************************************)
let inputstate opts =
  Option.iter (fun istate_file ->
    let fname = Loadpath.locate_file (CUnix.make_suffix istate_file ".coq") in
    States.intern_state fname) opts.inputstate

let outputstate opts =
  Option.iter (fun ostate_file ->
    let fname = CUnix.make_suffix ostate_file ".coq" in
    States.extern_state fname) opts.outputstate

(******************************************************************************)
(* Fatal Errors                                                               *)
(******************************************************************************)

(** Prints info which is either an error or an anomaly and then exits
    with the appropriate error code *)
let fatal_error_exn exn =
  Topfmt.(in_phase ~phase:Initialization print_err_exn exn);
  flush_all ();
  let exit_code =
    if CErrors.(is_anomaly exn || not (handled exn)) then 129 else 1
  in
  exit exit_code

(******************************************************************************)
(* Color Options                                                              *)
(******************************************************************************)
let init_color opts =
  let has_color = match opts.color with
  | `OFF -> false
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
      | None -> Topfmt.default_styles (); true        (** Default colors *)
      | Some "" -> false                              (** No color output *)
      | Some s -> Topfmt.parse_color_config s; true   (** Overwrite all colors *)
    end
    else
      false
  in
  if Proof_diffs.show_diffs () && not term_color && not opts.batch_mode then
    (prerr_endline "Error: -diffs requires enabling -color"; exit 1);
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
             Gc.minor_heap_size = 33554432; (** 4M *)
             Gc.space_overhead = 120}

(** Main init routine *)
let init_toplevel init_opts custom_init arglist =
  (* Coq's init process, phase 1:
     OCaml parameters, basic structures, and IO
   *)
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  let init_feeder = Feedback.add_feeder Coqloop.coqloop_feed in

  Lib.init();

  (* Coq's init process, phase 2:
     Basic Coq environment, load-path, plugins.
   *)
  let res = begin
    try
      let opts,extras = parse_args init_opts arglist in
      memory_stat := opts.memory_stat;

      (* If we have been spawned by the Spawn module, this has to be done
       * early since the master waits us to connect back *)
      Spawned.init_channels ();
      Envars.set_coqlib ~fail:(fun msg -> CErrors.user_err Pp.(str msg));
      if opts.print_where then begin
        print_endline (Envars.coqlib ());
        exit (exitcode opts)
      end;
      if opts.print_config then begin
        Envars.print_config stdout Coq_config.all_src_dirs;
        exit (exitcode opts)
      end;
      if opts.print_tags then begin
        print_style_tags opts;
        exit (exitcode opts)
      end;
      if opts.filter_opts then begin
        print_string (String.concat "\n" extras);
        exit 0;
      end;
      let top_lp = Coqinit.toplevel_init_load_path () in
      List.iter Mltop.add_coq_path top_lp;
      let opts, extras = custom_init ~opts extras in
      if not (CList.is_empty extras) then begin
        prerr_endline ("Don't know what to do with "^String.concat " " extras);
        prerr_endline "See -help for the list of supported options";
        exit 1
      end;
      Flags.if_verbose print_header ();
      Mltop.init_known_plugins ();
      Global.set_engagement opts.impredicative_set;
      Global.set_indices_matter opts.indices_matter;
      Global.set_VM opts.enable_VM;
      Global.set_native_compiler opts.enable_native_compiler;

      (* Allow the user to load an arbitrary state here *)
      inputstate opts;

      (* This state will be shared by all the documents *)
      Stm.init_core ();

      (* Coq init process, phase 3: Stm initialization, backtracking state.

         It is essential that the module system is in a consistent
         state before we take the first snapshot. This was not
         guaranteed in the past, but now is thanks to the STM API.

         We split the codepath here depending whether coqtop is called
         in interactive mode or not.  *)

      (* The condition for starting the interactive mode is a bit
         convoluted, we should really refactor batch/compilation_mode
         more. *)
      if (not opts.batch_mode || CList.(is_empty opts.compile_list))
      (* Interactive *)
      then begin
        let iload_path = build_load_path opts in
        let require_libs = require_libs opts in
        let stm_options = opts.stm_flags in
        let open Vernac.State in
        let doc, sid = Topfmt.(in_phase ~phase:LoadingPrelude)
            Stm.new_doc
            Stm.{ doc_type = Interactive opts.toplevel_name;
                  iload_path; require_libs; stm_options;
                } in
        let state = { doc; sid; proof = None; time = opts.time } in
        Some (Ccompile.load_init_vernaculars opts ~state), opts
      (* Non interactive: we perform a sequence of compilation steps *)
      end else begin
        Ccompile.compile_files opts;

        (* Allow the user to output an arbitrary state *)
        outputstate opts;
        None, opts
      end;
    with any ->
      flush_all();
      fatal_error_exn any
  end in
  Feedback.del_feeder init_feeder;
  res

type custom_toplevel =
  { init : opts:coq_cmdopts -> string list -> coq_cmdopts * string list
  ; run : opts:coq_cmdopts -> state:Vernac.State.t -> unit
  ; opts : Coqargs.coq_cmdopts
  }

let coqtop_init ~opts extra =
  init_color opts;
  CoqworkmgrApi.(init !async_proofs_worker_priority);
  opts, extra

let coqtop_toplevel =
  { init = coqtop_init
  ; run = Coqloop.loop
  ; opts = Coqargs.default_opts
  }

let start_coq custom =
  match init_toplevel custom.opts custom.init (List.tl (Array.to_list Sys.argv)) with
  (* Batch mode *)
  | Some state, opts when not opts.batch_mode ->
    custom.run ~opts ~state;
    exit 1
  | _ , opts ->
    flush_all();
    if opts.output_context then begin
      let sigma, env = Pfedit.get_current_context () in
      Feedback.msg_notice (Flags.(with_option raw_print (Prettyp.print_full_pure_context env) sigma) ++ fnl ())
    end;
    CProfile.print_profile ();
    exit 0
