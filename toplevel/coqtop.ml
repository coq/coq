(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

let warning s = Flags.(with_option warn Feedback.msg_warning (strbrk s))

(* Feedback received in the init stage, this is different as the STM
   will not be generally be initialized, thus stateid, etc... may be
   bogus. For now we just print to the console too *)
let coqtop_init_feed = Coqloop.coqloop_feed
let drop_last_doc = ref None

(* Default toplevel loop *)
let console_toploop_run opts ~state =
  (* We initialize the console only if we run the toploop_run *)
  let tl_feed = Feedback.add_feeder Coqloop.coqloop_feed in
  if Dumpglob.dump () then begin
    Flags.if_verbose warning "Dumpglob cannot be used in interactive mode.";
    Dumpglob.noglob ()
  end;
  let state = Coqloop.loop ~time:opts.time ~state in
  (* Initialise and launch the Ocaml toplevel *)
  drop_last_doc := Some state;
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  (* We let the feeder in place for users of Drop *)
  Feedback.del_feeder tl_feed

let toploop_run = ref console_toploop_run

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
      let load_vernac f = Vernac.load_vernac ~time:opts.time ~echo ~interactive:false ~check:true ~state f in
      if !Flags.beautify
      then Flags.with_option Flags.beautify_file load_vernac f_in
      else load_vernac s
    ) state (List.rev opts.load_vernacular_list)

let load_init_vernaculars opts ~state =
  let state = if opts.load_rcfile then
      Coqinit.load_rcfile ~rcfile:opts.rcfile ~time:opts.time ~state
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

let fatal_error_exn ?extra exn =
  Topfmt.print_err_exn ?extra exn;
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
let compile opts ~echo ~f_in ~f_out =
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

      let doc, sid = Stm.(new_doc
          { doc_type = VoDoc long_f_dot_vo;
            iload_path; require_libs; stm_options;
          }) in

      let state = { doc; sid; proof = None } in
      let state = load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      Aux_file.(start_aux_file
        ~aux_file:(aux_file_name_for long_f_dot_vo)
        ~v_file:long_f_dot_v);
      Dumpglob.start_dump_glob ~vfile:long_f_dot_v ~vofile:long_f_dot_vo;
      Dumpglob.dump_string ("F" ^ Names.DirPath.to_string ldir ^ "\n");
      let wall_clock1 = Unix.gettimeofday () in
      let state = Vernac.load_vernac ~time:opts.time ~echo ~check:true ~interactive:false ~state long_f_dot_v in
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

      let doc, sid = Stm.(new_doc
          { doc_type = VioDoc long_f_dot_vio;
            iload_path; require_libs; stm_options;
          }) in

      let state = { doc; sid; proof = None } in
      let state = load_init_vernaculars opts ~state in
      let ldir = Stm.get_ldir ~doc:state.doc in
      let state = Vernac.load_vernac ~time:opts.time ~echo ~check:false ~interactive:false ~state long_f_dot_v in
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

let compile opts ~echo ~f_in ~f_out =
  ignore(CoqworkmgrApi.get 1);
  compile opts ~echo ~f_in ~f_out;
  CoqworkmgrApi.giveback 1

let compile_file opts (f_in, echo) =
  if !Flags.beautify then
    Flags.with_option Flags.beautify_file
      (fun f_in -> compile opts ~echo ~f_in ~f_out:None) f_in
  else
    compile opts ~echo ~f_in ~f_out:None

let compile_files opts =
  let compile_list = List.rev opts.compile_list in
  List.iter (compile_file opts) compile_list

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
  (* We must add update the loadpath here as the scheduling process
     happens outside of the STM *)
  let iload_path = build_load_path opts in
  List.iter Mltop.add_coq_path iload_path;

  if opts.vio_checking then
    Vio_checking.schedule_vio_checking opts.vio_files_j opts.vio_files
  else
    Vio_checking.schedule_vio_compilation opts.vio_files_j opts.vio_files

(******************************************************************************)
(* Color Options                                                              *)
(******************************************************************************)
let init_color color_mode =
  let has_color = match color_mode with
  | `OFF -> false
  | `ON -> true
  | `AUTO ->
    Terminal.has_style Unix.stdout &&
    Terminal.has_style Unix.stderr &&
    (* emacs compilation buffer does not support colors by default,
       its TERM variable is set to "dumb". *)
    try Sys.getenv "TERM" <> "dumb" with Not_found -> false
  in
  if has_color then begin
    let colors = try Some (Sys.getenv "COQ_COLORS") with Not_found -> None in
    match colors with
    | None ->
      (** Default colors *)
      Topfmt.init_terminal_output ~color:true
    | Some "" ->
      (** No color output *)
      Topfmt.init_terminal_output ~color:false
    | Some s ->
      (** Overwrite all colors *)
      Topfmt.clear_styles ();
      Topfmt.parse_color_config s;
      Topfmt.init_terminal_output ~color:true
  end
  else
    Topfmt.init_terminal_output ~color:false

let toploop_init = ref begin fun opts x ->
  let () = init_color opts.color in
  let () = CoqworkmgrApi.init !WorkerLoop.async_proofs_worker_priority in
  x
  end

let print_style_tags opts =
  let () = init_color opts.color in
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
    minor heap is heavily sollicited. Unfortunately, the default size is far too
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
let init_toplevel arglist =
  (* Coq's init process, phase 1:
     OCaml parameters, basic structures, and IO
   *)
  CProfile.init_profile ();
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  let init_feeder = Feedback.add_feeder coqtop_init_feed in
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
      if opts.print_where then (print_endline(Envars.coqlib ()); exit(exitcode opts));
      if opts.print_config then (Envars.print_config stdout Coq_config.all_src_dirs; exit (exitcode opts));
      if opts.print_tags then (print_style_tags opts; exit (exitcode opts));
      if opts.filter_opts then (print_string (String.concat "\n" extras); exit 0);
      let top_lp = Coqinit.toplevel_init_load_path () in
      List.iter Mltop.add_coq_path top_lp;
      Option.iter Mltop.load_ml_object_raw opts.toploop;
      let extras = !toploop_init opts extras in
      if not (CList.is_empty extras) then begin
        prerr_endline ("Don't know what to do with "^String.concat " " extras);
        prerr_endline "See -help for the list of supported options";
        exit 1
      end;
      Flags.if_verbose print_header ();
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
        try
          let open Vernac.State in
          let doc, sid =
            Stm.(new_doc
                   { doc_type = Interactive opts.toplevel_name;
                     iload_path; require_libs; stm_options;
                   }) in
          let state = { doc; sid; proof = None } in
          Some (load_init_vernaculars opts ~state), opts
        with any -> flush_all(); fatal_error_exn any
      (* Non interactive: we perform a sequence of compilation steps *)
      end else begin
        try
          compile_files opts;
          (* Vio compile pass *)
          if opts.vio_files <> [] then schedule_vio opts;
          (* Vio task pass *)
          check_vio_tasks opts;
          (* Allow the user to output an arbitrary state *)
          outputstate opts;
          None, opts
        with any -> flush_all(); fatal_error_exn any
      end;
    with any ->
      flush_all();
      let extra = Some (str "Error during initialization: ") in
      fatal_error_exn ?extra any
  end in
  Feedback.del_feeder init_feeder;
  res

let start () =
  match init_toplevel (List.tl (Array.to_list Sys.argv)) with
  (* Batch mode *)
  | Some state, opts when not opts.batch_mode ->
    !toploop_run opts ~state;
    exit 1
  | _ , opts ->
    flush_all();
    if opts.output_context then begin
      let sigma, env = Pfedit.get_current_context () in
      Feedback.msg_notice (Flags.(with_option raw_print (Prettyp.print_full_pure_context env) sigma) ++ fnl ())
    end;
    CProfile.print_profile ();
    exit 0
