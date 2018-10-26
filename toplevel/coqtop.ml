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

(* Feedback received in the init stage, this is different as the STM
   will not be generally be initialized, thus stateid, etc... may be
   bogus. For now we just print to the console too *)
let coqtop_init_feed = Coqloop.coqloop_feed Topfmt.Initialization

let coqtop_doc_feed = Coqloop.coqloop_feed Topfmt.LoadingPrelude

let coqtop_rcfile_feed = Coqloop.coqloop_feed Topfmt.LoadingRcFile

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
(* Interactive Load File Simulation                                           *)
(******************************************************************************)
let load_vernacular opts ~state =
  List.fold_left
    (fun state (f_in, echo) ->
      let s = Loadpath.locate_file f_in in
      (* Should make the beautify logic clearer *)
      let load_vernac f = Vernac.load_vernac ~echo ~interactive:false ~check:true ~state f in
      if !Flags.beautify
      then Flags.with_option Flags.beautify_file load_vernac f_in
      else load_vernac s
    ) state (List.rev opts.load_vernacular_list)

let load_init_vernaculars cur_feeder opts ~state =
  let state =
    if opts.load_rcfile then begin
        Feedback.del_feeder !cur_feeder;
        let rc_feeder = Feedback.add_feeder coqtop_rcfile_feed in
        let state  = Coqinit.load_rcfile ~rcfile:opts.rcfile ~state in
        Feedback.del_feeder rc_feeder;
        cur_feeder := Feedback.add_feeder coqtop_init_feed;
        state
      end
    else begin
      Flags.if_verbose Feedback.msg_info (str"Skipping rcfile loading.");
      state
    end in

  load_vernacular opts ~state

(******************************************************************************)
(* Startup LoadPath and Modules                                               *)
(******************************************************************************)
(* prelude_data == From Coq Require Export Prelude. *)
let prelude_data = "Prelude", Some "Coq", Some true

let require_libs opts =
  if opts.load_init then prelude_data :: opts.vo_requires else opts.vo_requires

let cmdline_load_path opts =
  let open Mltop in
  (* loadpaths given by options -Q and -R *)
  List.map
    (fun (unix_path, coq_path, implicit) ->
       { recursive = true;
         path_spec = VoPath { unix_path; coq_path; has_ml = Mltop.AddNoML; implicit } })
      (List.rev opts.vo_includes) @

  (* additional ml directories, given with option -I *)
  List.map (fun s -> {recursive = false; path_spec = MlPath s}) (List.rev opts.ml_includes)

let build_load_path opts =
  Coqinit.libs_init_load_path ~load_init:opts.load_init @
  cmdline_load_path opts

(******************************************************************************)
(* Fatal Errors                                                               *)
(******************************************************************************)

(** Prints info which is either an error or an anomaly and then exits
    with the appropriate error code *)
let fatal_error msg =
  Topfmt.std_logger Feedback.Error msg;
  flush_all ();
  exit 1

let fatal_error_exn exn =
  Topfmt.print_err_exn Topfmt.Initialization exn;
  flush_all ();
  let exit_code =
    if CErrors.(is_anomaly exn || not (handled exn)) then 129 else 1
  in
  exit exit_code

(******************************************************************************)
(* File Compilation                                                           *)
(******************************************************************************)
let warn_file_no_extension =
  CWarnings.create ~name:"file-no-extension" ~category:"filesystem"
         (fun (f,ext) ->
          str "File \"" ++ str f ++
            strbrk "\" has been implicitly expanded to \"" ++
            str f ++ str ext ++ str "\"")

let ensure_ext ext f =
  if Filename.check_suffix f ext then f
  else begin
    warn_file_no_extension (f,ext);
    f ^ ext
  end

let chop_extension f =
  try Filename.chop_extension f with _ -> f

let ensure_bname src tgt =
  let src, tgt = Filename.basename src, Filename.basename tgt in
  let src, tgt = chop_extension src, chop_extension tgt in
  if src <> tgt then
    fatal_error (str "Source and target file names must coincide, directories can differ" ++ fnl () ++
                   str "Source: " ++ str src                                                ++ fnl () ++
                   str "Target: " ++ str tgt)

let ensure ext src tgt = ensure_bname src tgt; ensure_ext ext tgt

let ensure_v v = ensure ".v" v v
let ensure_vo v vo = ensure ".vo" v vo
let ensure_vio v vio = ensure ".vio" v vio

let ensure_exists f =
  if not (Sys.file_exists f) then
    fatal_error (hov 0 (str "Can't find file" ++ spc () ++ str f))

(* Compile a vernac file *)
let compile cur_feeder opts ~echo ~f_in ~f_out =
  let open Vernac.State in
  let check_pending_proofs () =
    let pfs = Proof_global.get_all_proof_names () in
    if not (CList.is_empty pfs) then
      fatal_error (str "There are pending proofs: "
                    ++ (pfs
                        |> List.rev
                        |> prlist_with_sep pr_comma Names.Id.print)
                    ++ str ".")
  in
  let iload_path = build_load_path opts in
  let require_libs = require_libs opts in
  let stm_options = opts.stm_flags in
  match opts.compilation_mode with
  | BuildVo ->
      Flags.record_aux_file := true;
      let long_f_dot_v = ensure_v f_in in
      ensure_exists long_f_dot_v;
      let long_f_dot_vo =
        match f_out with
        | None -> long_f_dot_v ^ "o"
        | Some f -> ensure_vo long_f_dot_v f in

      Feedback.del_feeder !cur_feeder;
      let doc_feeder = Feedback.add_feeder coqtop_doc_feed in
      let doc, sid =
        Stm.(new_doc
          { doc_type = VoDoc long_f_dot_vo;
            iload_path; require_libs; stm_options;
          }) in
      Feedback.del_feeder doc_feeder;
      cur_feeder := Feedback.add_feeder coqtop_init_feed;

      let state = { doc; sid; proof = None; time = opts.time } in
      let state = load_init_vernaculars cur_feeder opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_vo)
        ~v_file:long_f_dot_v);
      Dumpglob.start_dump_glob ~vfile:long_f_dot_v ~vofile:long_f_dot_vo;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");
      let wall_clock1 = Unix.gettimeofday () in
      let state = Vernac.load_vernac ~echo ~check:true ~interactive:false ~state long_f_dot_v in
      let _doc = Stm.join ~doc:state.doc in
      let wall_clock2 = Unix.gettimeofday () in
      check_pending_proofs ();
      Library.save_library_to ldir long_f_dot_vo (Global.opaque_tables ());
      Aux_file.record_in_aux_at "vo_compile_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      Aux_file.stop_aux_file ();
      Dumpglob.end_dump_glob ()

  | BuildVio ->
      Flags.record_aux_file := false;
      Dumpglob.noglob ();

      let long_f_dot_v = ensure_v f_in in
      ensure_exists long_f_dot_v;

      let long_f_dot_vio =
        match f_out with
        | None -> long_f_dot_v ^ "io"
        | Some f -> ensure_vio long_f_dot_v f in

      (* We need to disable error resiliency, otherwise some errors
         will be ignored in batch mode. c.f. #6707

         This is not necessary in the vo case as it fully checks the
         document anyways. *)
      let stm_options = let open Stm.AsyncOpts in
        { stm_options with
          async_proofs_cmd_error_resilience = false;
          async_proofs_tac_error_resilience = `None;
        } in

      Feedback.del_feeder !cur_feeder;
      let doc_feeder = Feedback.add_feeder coqtop_doc_feed in
      let doc, sid =
        Stm.(new_doc
          { doc_type = VioDoc long_f_dot_vio;
            iload_path; require_libs; stm_options;
          }) in
      Feedback.del_feeder doc_feeder;
      cur_feeder := Feedback.add_feeder coqtop_init_feed;

      let state = { doc; sid; proof = None; time = opts.time } in
      let state = load_init_vernaculars cur_feeder opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let state = Vernac.load_vernac ~echo ~check:false ~interactive:false ~state long_f_dot_v in
      let doc = Stm.finish ~doc:state.doc in
      check_pending_proofs ();
      let _doc = Stm.snapshot_vio ~doc ldir long_f_dot_vio in
      Stm.reset_task_queue ()

  | Vio2Vo ->
      let open Filename in
      Flags.record_aux_file := false;
      Dumpglob.noglob ();
      let f = if check_suffix f_in ".vio" then chop_extension f_in else f_in in
      let lfdv, sum, lib, univs, disch, tasks, proofs = Library.load_library_todo f in
      let univs, proofs = Stm.finish_tasks lfdv univs disch proofs tasks in
      Library.save_library_raw lfdv sum lib univs proofs

let compile cur_feeder opts ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile cur_feeder opts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file cur_feeder opts (f_in, echo) =
  let f_out = opts.compilation_output_name in
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile cur_feeder opts ~echo ~f_in ~f_out) f_in
  else
    compile cur_feeder opts ~echo ~f_in ~f_out

let compile_files cur_feeder opts =
  let compile_list = List.rev opts.compile_list in
  List.iter (compile_file cur_feeder opts) compile_list

(******************************************************************************)
(* VIO Dispatching                                                            *)
(******************************************************************************)
let check_vio_tasks opts =
  let rc =
    List.fold_left (fun acc t -> Vio_checking.check_vio t && acc)
      true (List.rev opts.vio_tasks) in
  if not rc then fatal_error Pp.(str "VIO Task Check failed")

(* vio files *)
let schedule_vio opts =
  if opts.vio_checking then
    Vio_checking.schedule_vio_checking opts.vio_files_j opts.vio_files
  else
    Vio_checking.schedule_vio_compilation opts.vio_files_j opts.vio_files

let do_vio opts =
  (* We must initialize the loadpath here as the vio scheduling
     process happens outside of the STM *)
  if opts.vio_files <> [] || opts.vio_tasks <> [] then
    let iload_path = build_load_path opts in
    List.iter Mltop.add_coq_path iload_path;

  (* Vio compile pass *)
  if opts.vio_files <> [] then schedule_vio opts;
  (* Vio task pass *)
  if opts.vio_tasks <> [] then check_vio_tasks opts


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
let init_toplevel custom_init arglist =
  (* Coq's init process, phase 1:
     OCaml parameters, basic structures, and IO
   *)
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  let init_feeder = ref (Feedback.add_feeder coqtop_init_feed) in
  Lib.init();

  (* Coq's init process, phase 2:
     Basic Coq environment, load-path, plugins.
   *)
  let res = begin
    try
      let opts,extras = parse_args arglist in
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
      Mltop.init_known_plugins ();
      Global.set_engagement opts.impredicative_set;

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
      if (not opts.batch_mode
          || CList.(is_empty opts.compile_list && is_empty opts.vio_files && is_empty opts.vio_tasks))
      (* Interactive *)
      then begin
        let iload_path = build_load_path opts in
        let require_libs = require_libs opts in
        let stm_options = opts.stm_flags in
        let open Vernac.State in
        Feedback.del_feeder !init_feeder;
        let doc_feeder = Feedback.add_feeder coqtop_doc_feed in
        let doc, sid =
          Stm.(new_doc
                 { doc_type = Interactive opts.toplevel_name;
                   iload_path; require_libs; stm_options;
                 }) in
        Feedback.del_feeder doc_feeder;
        init_feeder := Feedback.add_feeder coqtop_init_feed;
        let state = { doc; sid; proof = None; time = opts.time } in
        Some (load_init_vernaculars init_feeder opts ~state), opts
      (* Non interactive: we perform a sequence of compilation steps *)
      end else begin
        compile_files init_feeder opts;
        (* Careful this will modify the load-path and state so after
           this point some stuff may not be safe anymore. *)
        do_vio opts;
        (* Allow the user to output an arbitrary state *)
        outputstate opts;
        None, opts
      end;
    with any ->
      flush_all();
      fatal_error_exn any
  end in
  Feedback.del_feeder !init_feeder;
  res

type custom_toplevel = {
  init : opts:coq_cmdopts -> string list -> coq_cmdopts * string list;
  run : opts:coq_cmdopts -> state:Vernac.State.t -> unit;
}

let coqtop_init ~opts extra =
  init_color opts;
  CoqworkmgrApi.(init !async_proofs_worker_priority);
  if CList.is_empty extra then
    Flags.if_verbose print_header ();
  opts, extra

let coqtop_toplevel = { init = coqtop_init; run = Coqloop.loop; }

let start_coq custom =
  match init_toplevel custom.init (List.tl (Array.to_list Sys.argv)) with
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
