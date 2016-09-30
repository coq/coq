(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Flags
open Names
open Libnames
open States
open Coqinit

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

let warning s = with_option Flags.warn Feedback.msg_warning (strbrk s)

let toploop = ref None

let color : [`ON | `AUTO | `OFF] ref = ref `AUTO
let set_color = function
| "yes" | "on" -> color := `ON
| "no" | "off" -> color := `OFF
| "auto" -> color := `AUTO
| _ -> prerr_endline ("Error: on/off/auto expected after option color"); exit 1

let init_color () =
  let has_color = match !color with
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
      Ppstyle.init_color_output ();
      Feedback.set_logger Feedback.color_terminal_logger
    | Some "" ->
      (** No color output *)
      ()
    | Some s ->
      (** Overwrite all colors *)
      Ppstyle.clear_styles ();
      Ppstyle.parse_config s;
      Ppstyle.init_color_output ();
      Feedback.set_logger Feedback.color_terminal_logger
  end

let toploop_init = ref begin fun x ->
  let () = init_color () in
  let () = CoqworkmgrApi.(init !Flags.async_proofs_worker_priority) in
  x
  end

let toploop_run = ref (fun () ->
  if Dumpglob.dump () then begin
    if_verbose warning "Dumpglob cannot be used in interactive mode.";
    Dumpglob.noglob ()
  end;
  Coqloop.loop();
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop())

let output_context = ref false

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

let impredicative_set = ref Declarations.PredicativeSet
let set_impredicative_set c = impredicative_set := Declarations.ImpredicativeSet
let set_type_in_type () =
  let typing_flags = Environ.typing_flags (Global.env ()) in
  Global.set_typing_flags { typing_flags with Declarations.check_universes = false }
let engage () =
  Global.set_engagement !impredicative_set

let set_batch_mode () = batch_mode := true

let toplevel_default_name = DirPath.make [Id.of_string "Top"]
let toplevel_name = ref (Some toplevel_default_name)
let set_toplevel_name dir =
  if DirPath.is_empty dir then error "Need a non empty toplevel module name";
  toplevel_name := Some dir
let unset_toplevel_name () = toplevel_name := None

let remove_top_ml () = Mltop.remove ()

let warn_deprecated_inputstate =
  CWarnings.create ~name:"deprecated-inputstate" ~category:"deprecated"
         (fun () -> strbrk "The inputstate option is deprecated and discouraged.")

let inputstate = ref ""
let set_inputstate s =
  warn_deprecated_inputstate ();
  inputstate:=s
let inputstate () =
  if not (String.is_empty !inputstate) then
    let fname = Loadpath.locate_file (CUnix.make_suffix !inputstate ".coq") in
    intern_state fname

let warn_deprecated_outputstate =
  CWarnings.create ~name:"deprecated-outputstate" ~category:"deprecated"
         (fun () ->
          strbrk "The outputstate option is deprecated and discouraged.")

let outputstate = ref ""
let set_outputstate s =
  warn_deprecated_outputstate ();
  outputstate:=s
let outputstate () =
  if not (String.is_empty !outputstate) then
    let fname = CUnix.make_suffix !outputstate ".coq" in
    extern_state fname

let set_include d p implicit =
  let p = dirpath_of_string p in
  push_include d p implicit

let load_vernacular_list = ref ([] : (string * bool) list)
let add_load_vernacular verb s =
  load_vernacular_list := ((CUnix.make_suffix s ".v"),verb) :: !load_vernacular_list
let load_vernacular () =
  List.iter
    (fun (s,b) ->
      let s = Loadpath.locate_file s in
      if Flags.do_beautify () then
	with_option beautify_file (Vernac.load_vernac b) s
      else
	Vernac.load_vernac b s)
    (List.rev !load_vernacular_list)

let load_vernacular_obj = ref ([] : string list)
let add_vernac_obj s = load_vernacular_obj := s :: !load_vernacular_obj
let load_vernac_obj () =
  let map dir = Qualid (Loc.ghost, qualid_of_string dir) in
  Vernacentries.vernac_require None None (List.rev_map map !load_vernacular_obj)

let require_prelude () =
  let vo = Envars.coqlib () / "theories/Init/Prelude.vo" in
  let vio = Envars.coqlib () / "theories/Init/Prelude.vio" in
  let m =
    if Sys.file_exists vo then vo else
    if Sys.file_exists vio then vio else vo in
  Library.require_library_from_dirpath [Coqlib.prelude_module,m] (Some true)

let require_list = ref ([] : string list)
let add_require s = require_list := s :: !require_list
let require () =
  let () = if !load_init then silently require_prelude () in
  let map dir = Qualid (Loc.ghost, qualid_of_string dir) in
  Vernacentries.vernac_require None (Some false) (List.rev_map map !require_list)

let add_compat_require v =
  match v with
  | Flags.V8_4 -> add_require "Coq.Compat.Coq84"
  | Flags.V8_5 -> add_require "Coq.Compat.Coq85"
  | _ -> ()

let compile_list = ref ([] : (bool * string) list)

let glob_opt = ref false

let add_compile verbose s =
  set_batch_mode ();
  Flags.make_silent true;
  if not !glob_opt then Dumpglob.dump_to_dotglob ();
  (** make the file name explicit; needed not to break up Coq loadpath stuff. *)
  let s =
    let open Filename in
    if is_implicit s
    then concat current_dir_name s
    else s
  in
  compile_list := (verbose,s) :: !compile_list

let compile_file (v,f) =
  if Flags.do_beautify () then
    with_option beautify_file (Vernac.compile v) f
  else
    Vernac.compile v f

let compile_files () =
  if !compile_list == [] then ()
  else
    let init_state = States.freeze ~marshallable:`No in
    let coqdoc_init_state = CLexer.location_table () in
    Feedback.(add_feeder debug_feeder);
    List.iter (fun vf ->
        States.unfreeze init_state;
        CLexer.restore_location_table coqdoc_init_state;
        compile_file vf)
      (List.rev !compile_list)

(** Options for proof general *)

let set_emacs () =
  if not (Option.is_empty !toploop) then
    error "Flag -emacs is incompatible with a custom toplevel loop";
  Flags.print_emacs := true;
  Feedback.(set_logger emacs_logger);
  Vernacentries.qed_display_script := false;
  color := `OFF

(** Options for CoqIDE *)

let set_ideslave () =
  if !Flags.print_emacs then error "Flags -ideslave and -emacs are incompatible";
  toploop := Some "coqidetop";
  Flags.ide_slave := true

(** Options for slaves *)

let set_toploop name =
  if !Flags.print_emacs then error "Flags -toploop and -emacs are incompatible";
  toploop := Some name

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

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let usage () =
  Envars.set_coqlib CErrors.error;
  init_load_path ();
  if !batch_mode then Usage.print_usage_coqc ()
  else begin
    Mltop.load_ml_objects_raw_rex
      (Str.regexp (if Mltop.is_native then "^.*top.cmxs$" else "^.*top.cma$"));
    Usage.print_usage_coqtop ()
  end

let print_style_tags () =
  let () = init_color () in
  let tags = Ppstyle.dump () in
  let iter (t, st) =
    let st = match st with Some st -> st | None -> Terminal.make () in
    let opt =
      Terminal.eval st ^
      String.concat "." (Ppstyle.repr t) ^
      Terminal.reset ^ "\n"
    in
    print_string opt
  in
  let make (t, st) = match st with
  | None -> None
  | Some st ->
    let tags = List.map string_of_int (Terminal.repr st) in
    let t = String.concat "." (Ppstyle.repr t) in
    Some (t ^ "=" ^ String.concat ";" tags)
  in
  let repr = List.map_filter make tags in
  let () = Printf.printf "COQ_COLORS=\"%s\"\n" (String.concat ":" repr) in
  let () = List.iter iter tags in
  flush_all ()

let error_missing_arg s =
  prerr_endline ("Error: extra argument expected after option "^s);
  prerr_endline "See -help for the syntax of supported options";
  exit 1

let filter_opts = ref false
let exitcode () = if !filter_opts then 2 else 0

let verb_compat_ntn = ref false
let no_compat_ntn = ref false

let print_where = ref false
let print_config = ref false
let print_tags = ref false

let get_priority opt s =
  try Flags.priority_of_string s
  with Invalid_argument _ ->
    prerr_endline ("Error: low/high expected after "^opt); exit 1

let get_async_proofs_mode opt = function
  | "no" | "off" -> Flags.APoff
  | "yes" | "on" -> Flags.APon
  | "lazy" -> Flags.APonLazy
  | _ -> prerr_endline ("Error: on/off/lazy expected after "^opt); exit 1

let get_cache opt = function
  | "force" -> Some Flags.Force
  | _ -> prerr_endline ("Error: force expected after "^opt); exit 1


let set_worker_id opt s =
  assert (s <> "master");
  Flags.async_proofs_worker_id := s

let get_bool opt = function
  | "yes" | "on" -> true
  | "no" | "off" -> false
  | _ -> prerr_endline ("Error: yes/no expected after option "^opt); exit 1

let get_int opt n =
  try int_of_string n
  with Failure _ ->
    prerr_endline ("Error: integer expected after option "^opt); exit 1

let get_float opt n =
  try float_of_string n
  with Failure _ ->
    prerr_endline ("Error: float expected after option "^opt); exit 1

let get_host_port opt s =
  match CString.split ':' s with
  | [host; portr; portw] ->
       Some (Spawned.Socket(host, int_of_string portr, int_of_string portw))
  | ["stdfds"] -> Some Spawned.AnonPipe
  | _ ->
     prerr_endline ("Error: host:portr:portw or stdfds expected after option "^opt);
     exit 1

let get_error_resilience opt = function
  | "on" | "all" | "yes" -> `All
  | "off" | "no" -> `None
  | s -> `Only (String.split ',' s)

let get_task_list s = List.map int_of_string (Str.split (Str.regexp ",") s)

let vio_tasks = ref []

let add_vio_task f =
  set_batch_mode ();
  Flags.make_silent true;
  vio_tasks := f :: !vio_tasks

let check_vio_tasks () =
  let rc =
    List.fold_left (fun acc t -> Vio_checking.check_vio t && acc)
      true (List.rev !vio_tasks) in
  if not rc then exit 1

let vio_files = ref []
let vio_files_j = ref 0
let vio_checking = ref false
let add_vio_file f =
  set_batch_mode ();
  Flags.make_silent true;
  vio_files := f :: !vio_files

let set_vio_checking_j opt j =
  try vio_files_j := int_of_string j
  with Failure _ ->
    prerr_endline ("The first argument of " ^ opt ^ " must the number");
    prerr_endline "of concurrent workers to be used (a positive integer).";
    prerr_endline "Makefiles generated by coq_makefile should be called";
    prerr_endline "setting the J variable like in 'make vio2vo J=3'";
    exit 1

let is_not_dash_option = function
  | Some f when String.length f > 0 && f.[0] <> '-' -> true
  | _ -> false

let schedule_vio_checking () =
  if !vio_files <> [] && !vio_checking then
    Vio_checking.schedule_vio_checking !vio_files_j !vio_files
let schedule_vio_compilation () =
  if !vio_files <> [] && not !vio_checking then
    Vio_checking.schedule_vio_compilation !vio_files_j !vio_files

let get_native_name s =
  (* We ignore even critical errors because this mode has to be super silent *)
  try
    String.concat "/" [Filename.dirname s;
      Nativelib.output_dir; Library.native_name_from_filename s]
  with _ -> ""

let parse_args arglist =
  let args = ref arglist in
  let extras = ref [] in
  let rec parse () = match !args with
  | [] -> List.rev !extras
  | opt :: rem ->
    args := rem;
    let next () = match !args with
      | x::rem -> args := rem; x
      | [] -> error_missing_arg opt
    in
    let peek_next () = match !args with
      | x::_ -> Some x
      | [] -> None
    in
    begin match opt with

    (* Complex options with many args *)
    |"-I"|"-include" ->
      begin match rem with
      | d :: rem -> push_ml_include d; args := rem
      | [] -> error_missing_arg opt
      end
    |"-Q" ->
      begin match rem with
      | d :: p :: rem -> set_include d p false; args := rem
      | _ -> error_missing_arg opt
      end
    |"-R" ->
      begin match rem with
      | d :: p :: rem -> set_include d p true; args := rem
      | _ -> error_missing_arg opt
      end

    (* Options with two arg *)
    |"-check-vio-tasks" ->
        let tno = get_task_list (next ()) in
        let tfile = next () in
        add_vio_task (tno,tfile)
    |"-schedule-vio-checking" ->
        vio_checking := true;
        set_vio_checking_j opt (next ());
        add_vio_file (next ());
        while is_not_dash_option (peek_next ()) do add_vio_file (next ()); done
    |"-schedule-vio2vo" ->
        set_vio_checking_j opt (next ());
        add_vio_file (next ());
        while is_not_dash_option (peek_next ()) do add_vio_file (next ()); done

    (* Options with one arg *)
    |"-coqlib" -> Flags.coqlib_spec:=true; Flags.coqlib:=(next ())
    |"-async-proofs" ->
        Flags.async_proofs_mode := get_async_proofs_mode opt (next())
    |"-async-proofs-j" ->
        Flags.async_proofs_n_workers := (get_int opt (next ()))
    |"-async-proofs-cache" ->
        Flags.async_proofs_cache := get_cache opt (next ())
    |"-async-proofs-tac-j" ->
        Flags.async_proofs_n_tacworkers := (get_int opt (next ()))
    |"-async-proofs-worker-priority" ->
        Flags.async_proofs_worker_priority := get_priority opt (next ())
    |"-async-proofs-private-flags" ->
        Flags.async_proofs_private_flags := Some (next ());
    |"-async-proofs-tactic-error-resilience" ->
        Flags.async_proofs_tac_error_resilience := get_error_resilience opt (next ())
    |"-async-proofs-command-error-resilience" ->
        Flags.async_proofs_cmd_error_resilience := get_bool opt (next ())
    |"-async-proofs-delegation-threshold" ->
        Flags.async_proofs_delegation_threshold:= get_float opt (next ())
    |"-worker-id" -> set_worker_id opt (next ())
    |"-compat" -> let v = get_compat_version (next ()) in Flags.compat_version := v; add_compat_require v
    |"-compile" -> add_compile false (next ())
    |"-compile-verbose" -> add_compile true (next ())
    |"-dump-glob" -> Dumpglob.dump_into_file (next ()); glob_opt := true
    |"-feedback-glob" -> Dumpglob.feedback_glob ()
    |"-exclude-dir" -> System.exclude_directory (next ())
    |"-init-file" -> set_rcfile (next ())
    |"-inputstate"|"-is" -> set_inputstate (next ())
    |"-load-ml-object" -> Mltop.dir_ml_load (next ())
    |"-load-ml-source" -> Mltop.dir_ml_use (next ())
    |"-load-vernac-object" -> add_vernac_obj (next ())
    |"-load-vernac-source"|"-l" -> add_load_vernacular false (next ())
    |"-load-vernac-source-verbose"|"-lv" -> add_load_vernacular true (next ())
    |"-outputstate" -> set_outputstate (next ())
    |"-print-mod-uid" -> let s = String.concat " " (List.map get_native_name rem) in print_endline s; exit 0
    |"-require" -> add_require (next ())
    |"-top" -> set_toplevel_name (dirpath_of_string (next ()))
    |"-with-geoproof" -> Coq_config.with_geoproof := get_bool opt (next ())
    |"-main-channel" -> Spawned.main_channel := get_host_port opt (next())
    |"-control-channel" -> Spawned.control_channel := get_host_port opt (next())
    |"-vio2vo" -> add_compile false (next ()); Flags.compilation_mode := Vio2Vo
    |"-toploop" -> set_toploop (next ())
    |"-w" | "-W" -> CWarnings.set_flags (next ())
    |"-o" -> Flags.compilation_output_name := Some (next())

    (* Options with zero arg *)
    |"-async-queries-always-delegate"
    |"-async-proofs-always-delegate"
    |"-async-proofs-full" ->
        Flags.async_proofs_full := true;
    |"-async-proofs-never-reopen-branch" ->
        Flags.async_proofs_never_reopen_branch := true;
    |"-batch" -> set_batch_mode ()
    |"-test-mode" -> test_mode := true
    |"-beautify" -> make_beautify true
    |"-boot" -> boot := true; no_load_rc ()
    |"-bt" -> Backtrace.record_backtrace true
    |"-color" -> set_color (next ())
    |"-config"|"--config" -> print_config := true
    |"-debug" -> set_debug ()
    |"-emacs" -> set_emacs ()
    |"-filteropts" -> filter_opts := true
    |"-h"|"-H"|"-?"|"-help"|"--help" -> usage ()
    |"-ideslave" -> set_ideslave ()
    |"-impredicative-set" -> set_impredicative_set ()
    |"-indices-matter" -> Indtypes.enforce_indices_matter ()
    |"-just-parsing" -> Vernac.just_parsing := true
    |"-m"|"--memory" -> memory_stat := true
    |"-noinit"|"-nois" -> load_init := false
    |"-no-compat-notations" -> no_compat_ntn := true
    |"-no-glob"|"-noglob" -> Dumpglob.noglob (); glob_opt := true
    |"-native-compiler" ->
      if Coq_config.no_native_compiler then
	warning "Native compilation was disabled at configure time."
      else native_compiler := true
    |"-notop" -> unset_toplevel_name ()
    |"-output-context" -> output_context := true
    |"-profile-ltac" -> Flags.profile_ltac := true
    |"-q" -> no_load_rc ()
    |"-quiet"|"-silent" -> Flags.make_silent true; Flags.make_warn false
    |"-quick" -> Flags.compilation_mode := BuildVio
    |"-list-tags" -> print_tags := true
    |"-time" -> Flags.time := true
    |"-type-in-type" -> set_type_in_type ()
    |"-unicode" -> add_require "Utf8_core"
    |"-v"|"--version" -> Usage.version (exitcode ())
    |"--print-version" -> Usage.machine_readable_version (exitcode ())
    |"-verbose-compat-notations" -> verb_compat_ntn := true
    |"-where" -> print_where := true
    |"-xml" -> Flags.xml_export := true

    (* Deprecated options *)
    |"-byte" -> warning "option -byte deprecated, call with .byte suffix"
    |"-opt" -> warning "option -opt deprecated, call with .opt suffix"
    |"-full" -> warning "option -full deprecated"
    |"-notactics" -> warning "Obsolete option \"-notactics\"."; remove_top_ml ()
    |"-emacs-U" ->
      warning "Obsolete option \"-emacs-U\", use -emacs instead."; set_emacs ()
    |"-v7" -> error "This version of Coq does not support v7 syntax"
    |"-v8" -> warning "Obsolete option \"-v8\"."
    |"-lazy-load-proofs" -> warning "Obsolete option \"-lazy-load-proofs\"."
    |"-dont-load-proofs" -> warning "Obsolete option \"-dont-load-proofs\"."
    |"-force-load-proofs" -> warning "Obsolete option \"-force-load-proofs\"."
    |"-unsafe" -> warning "Obsolete option \"-unsafe\"."; ignore (next ())
    |"-quality" -> warning "Obsolete option \"-quality\"."

    (* Unknown option *)
    | s -> extras := s :: !extras
    end;
    parse ()
  in
  try
    parse ()
  with
    | UserError(_, s) as e ->
      if is_empty s then exit 1
      else fatal_error (CErrors.print e) false
    | any -> fatal_error (CErrors.print any) (CErrors.is_anomaly any)

let init_toplevel arglist =
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init();
  (* Default Proofb Mode starts with an alternative default. *)
  Goptions.set_string_option_value ["Default";"Proof";"Mode"] "Classic";
  begin
    try
      let extras = parse_args arglist in
      (* If we have been spawned by the Spawn module, this has to be done
       * early since the master waits us to connect back *)
      Spawned.init_channels ();
      Envars.set_coqlib CErrors.error;
      if !print_where then (print_endline(Envars.coqlib ()); exit(exitcode ()));
      if !print_config then (Usage.print_config (); exit (exitcode ()));
      if !print_tags then (print_style_tags (); exit (exitcode ()));
      if !filter_opts then (print_string (String.concat "\n" extras); exit 0);
      init_load_path ();
      Option.iter Mltop.load_ml_object_raw !toploop;
      let extras = !toploop_init extras in
      if not (List.is_empty extras) then begin
        prerr_endline ("Don't know what to do with "^String.concat " " extras);
        prerr_endline "See -help for the list of supported options";
        exit 1
      end;
      if_verbose print_header ();
      inputstate ();
      Mltop.init_known_plugins ();
      engage ();
      (* Be careful to set these variables after the inputstate *)
      Syntax_def.set_verbose_compat_notations !verb_compat_ntn;
(*       Syntax_def.set_compat_notations (not !no_compat_ntn); FIXME *)
      if (not !batch_mode || List.is_empty !compile_list)
         && Global.env_is_initial ()
      then Option.iter Declaremods.start_library !toplevel_name;
      init_library_roots ();
      load_vernac_obj ();
      require ();
      Stm.init ();
      load_rcfile();
      load_vernacular ();
      compile_files ();
      schedule_vio_checking ();
      schedule_vio_compilation ();
      check_vio_tasks ();
      outputstate ()
    with any ->
      let any = CErrors.push any in
      flush_all();
      let msg =
        if !batch_mode then mt ()
        else str "Error during initialization:" ++ fnl ()
      in
      let is_anomaly e = CErrors.is_anomaly e || not (CErrors.handled e) in
      fatal_error (msg ++ Coqloop.print_toplevel_error any) (is_anomaly (fst any))
  end;
  if !batch_mode then begin
    flush_all();
    if !output_context then
      Feedback.msg_notice (with_option raw_print Prettyp.print_full_pure_context () ++ fnl ());
    Profile.print_profile ();
    exit 0
  end

let start () =
  let () = init_toplevel (List.tl (Array.to_list Sys.argv)) in
  (* In batch mode, Coqtop has already exited at this point. In interactive one,
     dump glob is nothing but garbage ...  *)
  !toploop_run ();
  exit 1

(* [Coqtop.start] will be called by the code produced by coqmktop *)
