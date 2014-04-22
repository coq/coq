(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open System
open Flags
open Names
open Libnames
open States
open Coqinit

let () = at_exit flush_all

let ( / ) = Filename.concat

let fatal_error info =
  pperrnl info; flush_all (); exit 1

let get_version_date () =
  try
    let ch = open_in (Envars.coqlib () / "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
    let () = close_in ch in
    (ver,rev)
  with e when Errors.noncritical e ->
    (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = get_version_date () in
  ppnl (str ("Welcome to Coq "^ver^" ("^rev^")"));
  pp_flush ()

let output_context = ref false

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then
    ppnl
      (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes")

let _ = at_exit print_memory_stat

let engagement = ref None
let set_engagement c = engagement := Some c
let engage () =
  match !engagement with Some c -> Global.set_engagement c | None -> ()

let set_batch_mode () = batch_mode := true

let toplevel_default_name = DirPath.make [Id.of_string "Top"]
let toplevel_name = ref (Some toplevel_default_name)
let set_toplevel_name dir =
  if DirPath.is_empty dir then error "Need a non empty toplevel module name";
  toplevel_name := Some dir
let unset_toplevel_name () = toplevel_name := None

let remove_top_ml () = Mltop.remove ()

let inputstate = ref ""
let set_inputstate s = inputstate:=s
let inputstate () = if not (String.is_empty !inputstate) then intern_state !inputstate

let outputstate = ref ""
let set_outputstate s = outputstate:=s
let outputstate () = if not (String.is_empty !outputstate) then extern_state !outputstate

let set_include d p recursive implicit =
  let p = dirpath_of_string p in
  push_include d p recursive implicit

let load_vernacular_list = ref ([] : (string * bool) list)
let add_load_vernacular verb s =
  load_vernacular_list := ((CUnix.make_suffix s ".v"),verb) :: !load_vernacular_list
let load_vernacular () =
  List.iter
    (fun (s,b) ->
      if Flags.do_beautify () then
	with_option beautify_file (Vernac.load_vernac b) s
      else
	Vernac.load_vernac b s)
    (List.rev !load_vernacular_list)

let load_vernacular_obj = ref ([] : string list)
let add_vernac_obj s = load_vernacular_obj := s :: !load_vernacular_obj
let load_vernac_obj () =
  List.iter (fun f -> Library.require_library_from_file None f None)
    (List.rev !load_vernacular_obj)

let require_prelude () =
  let vo = Envars.coqlib () / "theories/Init/Prelude.vo" in
  Library.require_library_from_dirpath [Coqlib.prelude_module,vo] (Some true)

let require_list = ref ([] : string list)
let add_require s = require_list := s :: !require_list
let require () =
  if !load_init then silently require_prelude ();
  List.iter (fun s -> Library.require_library_from_file None s (Some false))
    (List.rev !require_list)

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
  match !compile_list with
    | [] -> ()
    | [vf] -> compile_file vf (* One compilation : no need to save init state *)
    | l ->
      let init_state = States.freeze ~marshallable:`No in
      let coqdoc_init_state = Lexer.location_table () in
      List.iter
        (fun vf ->
	  States.unfreeze init_state;
	  Lexer.restore_location_table coqdoc_init_state;
          compile_file vf)
        (List.rev l)

(*s options for the virtual machine *)

let boxed_val = ref false
let use_vm = ref false

let set_vm_opt () =
  Vm.set_transp_values (not !boxed_val);
  Vconv.set_use_vm !use_vm

(** Options for proof general *)

let set_emacs () =
  Flags.print_emacs := true;
  Pp.make_pp_emacs ();
  Vernacentries.qed_display_script := false;
  Flags.make_term_color false

(** GC tweaking *)

(** Coq is a heavy user of persistent data structures and symbolic ASTs, so the
    minor heap is heavily sollicited. Unfortunately, the default size is far too
    small, so we enlarge it a lot (128 times larger).

    To better handle huge memory consumers, we also augment the default major
    heap increment and the GC pressure coefficient.
*)

let init_gc () =
  let param =
    try ignore (Sys.getenv "OCAMLRUNPARAM"); true
    with Not_found -> false
  in
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
(*     Gc.major_heap_increment = 268435456; (** 32M *) *)
    Gc.space_overhead = 120;
  } in
  if param then ()
  else Gc.set tweaked_control

(*s Parsing of the command line.
    We no longer use [Arg.parse], in order to use share [Usage.print_usage]
    between coqtop and coqc. *)

let usage () =
  if !batch_mode then
    Usage.print_usage_coqc ()
  else
    Usage.print_usage_coqtop () ;
  flush stderr ;
  exit 1

let error_missing_arg s =
  prerr_endline ("Error: extra argument expected after option "^s);
  prerr_endline "See --help for the syntax of supported options";
  exit 1

let warning s = msg_warning (strbrk s)

let filter_opts = ref false
let exitcode () = if !filter_opts then 2 else 0

let verb_compat_ntn = ref false
let no_compat_ntn = ref false

let print_where = ref false
let print_config = ref false

let get_async_proofs_mode opt next = function
  | "off" -> Flags.APoff
  | "on" -> Flags.APonParallel 0
  | "worker" ->
      let n = int_of_string (next()) in assert (n > 0);
      Flags.APonParallel n
  | "lazy" -> Flags.APonLazy
  | _ -> prerr_endline ("Error: on/off/lazy/worker expected after "^opt); exit 1

let get_bool opt = function
  | "yes" -> true
  | "no" -> false
  | _ -> prerr_endline ("Error: yes/no expected after option "^opt); exit 1

let get_int opt n =
  try int_of_string n
  with Failure _ ->
    prerr_endline ("Error: integer expected after option "^opt); exit 1

let get_host_port opt s =
  match CString.split ':' s with
  | [host; port] -> Some (Spawned.Socket(host, int_of_string port))
  | ["stdfds"] -> Some Spawned.AnonPipe
  | _ ->
     prerr_endline ("Error: host:port or stdfds expected after option "^opt);
     exit 1

let get_task_list s = List.map int_of_string (Str.split (Str.regexp ",") s)

let vi_tasks = ref []

let add_vi_task f =
  set_batch_mode ();
  Flags.make_silent true;
  vi_tasks := f :: !vi_tasks

let check_vi_tasks () =
  let rc =
    List.fold_left (fun acc t -> Vi_checking.check_vi t && acc)
      true (List.rev !vi_tasks) in
  if not rc then exit 1

let vi_files = ref []
let vi_files_j = ref 0
let vi_checking = ref false
let add_vi_file f =
  set_batch_mode ();
  Flags.make_silent true;
  vi_files := f :: !vi_files
let set_vi_checking_j opt j =
  try vi_files_j := int_of_string j
  with Failure _ ->
    prerr_endline ("The first argument of " ^ opt ^ " must the number");
    prerr_endline "of concurrent workers to be used (a positive integer).";
    prerr_endline "Makefiles generated by coq_makefile should be called";
    prerr_endline "setting the J variable like in 'make vi2vo J=3'";
    exit 1

let is_not_dash_option = function
  | Some f when String.length f > 0 && f.[0] <> '-' -> true
  | _ -> false

let schedule_vi_checking () =
  if !vi_files <> [] && !vi_checking then
    Vi_checking.schedule_vi_checking !vi_files_j !vi_files
let schedule_vi_compilation () =
  if !vi_files <> [] && not !vi_checking then
    Vi_checking.schedule_vi_compilation !vi_files_j !vi_files

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
      | d :: "-as" :: p :: rem -> set_include d p false true; args := rem
      | d :: "-as" :: [] -> error_missing_arg "-as"
      | d :: rem -> push_ml_include d; args := rem
      | [] -> error_missing_arg opt
      end
    |"-Q" ->
      begin match rem with
      | d :: p :: rem -> set_include d p true false; args := rem
      | _ -> error_missing_arg opt
      end
    |"-R" ->
      begin match rem with
      | d :: "-as" :: [] -> error_missing_arg "-as"
      | d :: "-as" :: p :: rem
      | d :: p :: rem -> set_include d p true true; args := rem
      | _ -> error_missing_arg opt
      end

    (* Options with two arg *)
    |"-check-vi-tasks" ->
        let tno = get_task_list (next ()) in
        let tfile = next () in
        add_vi_task (tno,tfile)
    |"-schedule-vi-checking" ->
        vi_checking := true;
        set_vi_checking_j opt (next ());
        add_vi_file (next ());
        while is_not_dash_option (peek_next ()) do add_vi_file (next ()); done
    |"-schedule-vi2vo" ->
        set_vi_checking_j opt (next ());
        add_vi_file (next ());
        while is_not_dash_option (peek_next ()) do add_vi_file (next ()); done

    (* Options with one arg *)
    |"-coqlib" -> Flags.coqlib_spec:=true; Flags.coqlib:=(next ())
    |"-async-proofs" ->
        Flags.async_proofs_mode := get_async_proofs_mode opt next (next())
    |"-async-proofs-j" ->
        Flags.async_proofs_n_workers := (get_int opt (next ()))
    |"-async-proofs-worker-flags" ->
        Flags.async_proofs_worker_flags := Some (next ())
    |"-compat" -> Flags.compat_version := get_compat_version (next ())
    |"-compile" -> add_compile false (next ())
    |"-compile-verbose" -> add_compile true (next ())
    |"-dump-glob" -> Dumpglob.dump_into_file (next ()); glob_opt := true
    |"-feedback-glob" -> Dumpglob.feedback_glob ()
    |"-exclude-dir" -> exclude_search_in_dirname (next ())
    |"-init-file" -> set_rcfile (next ())
    |"-inputstate"|"-is" -> set_inputstate (next ())
    |"-load-ml-object" -> Mltop.dir_ml_load (next ())
    |"-load-ml-source" -> Mltop.dir_ml_use (next ())
    |"-load-vernac-object" -> add_vernac_obj (next ())
    |"-load-vernac-source"|"-l" -> add_load_vernacular false (next ())
    |"-load-vernac-source-verbose"|"-lv" -> add_load_vernacular true (next ())
    |"-outputstate" -> set_outputstate (next ())
    |"-print-mod-uid" -> Flags.print_mod_uid := true; add_require (next ())
    |"-require" -> add_require (next ())
    |"-top" -> set_toplevel_name (dirpath_of_string (next ()))
    |"-unsafe" -> add_unsafe (next ())
    |"-with-geoproof" -> Coq_config.with_geoproof := get_bool opt (next ())
    |"-main-channel" -> Spawned.main_channel := get_host_port opt (next())
    |"-control-channel" -> Spawned.control_channel := get_host_port opt (next())
    |"-vi2vo" -> add_compile false (next ()); Flags.compilation_mode := Vi2Vo

    (* Options with zero arg *)
    |"-batch" -> set_batch_mode ()
    |"-beautify" -> make_beautify true
    |"-boot" -> boot := true; no_load_rc ()
    |"-bt" -> Backtrace.record_backtrace true
    |"-color" -> Flags.make_term_color true
    |"-config"|"--config" -> print_config := true
    |"-debug" -> set_debug ()
    |"-dont-load-proofs" -> Flags.load_proofs := Flags.Dont
    |"-emacs" -> set_emacs ()
    |"-filteropts" -> filter_opts := true
    |"-force-load-proofs" -> Flags.load_proofs := Flags.Force
    |"-h"|"-H"|"-?"|"-help"|"--help" -> usage ()
    |"--help-XML-protocol" ->
        Serialize.document Xml_printer.to_string_fmt; exit 0
    |"-ideslave" -> Flags.ide_slave := true
    |"-impredicative-set" -> set_engagement Declarations.ImpredicativeSet
    |"-just-parsing" -> Vernac.just_parsing := true
    |"-lazy-load-proofs" -> Flags.load_proofs := Flags.Lazy
    |"-m"|"--memory" -> memory_stat := true
    |"-noinit"|"-nois" -> load_init := false
    |"-no-compat-notations" -> no_compat_ntn := true
    |"-no-glob"|"-noglob" -> Dumpglob.noglob (); glob_opt := true
    |"-no-native-compiler" -> no_native_compiler := true
    |"-notop" -> unset_toplevel_name ()
    |"-output-context" -> output_context := true
    |"-q" -> no_load_rc ()
    |"-quality" -> term_quality := true; no_load_rc ()
    |"-quiet"|"-silent" -> Flags.make_silent true
    |"-quick" -> Flags.compilation_mode := BuildVi
    |"-time" -> Flags.time := true
    |"-unicode" -> add_require "Utf8_core"
    |"-v"|"--version" -> Usage.version (exitcode ())
    |"-verbose-compat-notations" -> verb_compat_ntn := true
    |"-vm" -> use_vm := true
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
      else fatal_error (Errors.print e)
    | any -> fatal_error (Errors.print any)

let init arglist =
  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init();
  (* Default Proofb Mode starts with an alternative default. *)
  Goptions.set_string_option_value ["Default";"Proof";"Mode"] "Classic";
  begin
    try
      let extras = parse_args arglist in
      if not (List.is_empty extras) && not !filter_opts then begin
        prerr_endline ("Don't know what to do with " ^ String.concat " " extras);
        prerr_endline "See --help for the list of supported options";
        exit 1
      end;
      (* If we have been spawned by the Spawn module, this has to be done
       * early since the master waits us to connect back *)
      Spawned.init_channels ();
      Envars.set_coqlib Errors.error;
      if !print_where then (print_endline (Envars.coqlib ()); exit (exitcode ()));
      if !print_config then (Usage.print_config (); exit (exitcode ()));
      if !filter_opts then (print_string (String.concat "\n" extras); exit 0);
      if !Flags.ide_slave then begin
        Flags.make_silent true;
        Ide_slave.init_stdout ()
      end else if Flags.async_proofs_is_worker () then begin
        Flags.make_silent true;
        Stm.slave_init_stdout ()
      end;
      if_verbose print_header ();
      init_load_path ();
      inputstate ();
      Mltop.init_known_plugins ();
      set_vm_opt ();
      engage ();
      (* Be careful to set these variables after the inputstate *)
      Syntax_def.set_verbose_compat_notations !verb_compat_ntn;
      Syntax_def.set_compat_notations (not !no_compat_ntn);
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
      schedule_vi_checking ();
      schedule_vi_compilation ();
      check_vi_tasks ();
      outputstate ()
    with any ->
      flush_all();
      let msg =
        if !batch_mode then mt ()
        else str "Error during initialization:" ++ fnl ()
      in
      fatal_error (msg ++ Coqloop.print_toplevel_error any)
  end;
  if !batch_mode then begin
    flush_all();
    if !output_context then
      Pp.ppnl (with_option raw_print Prettyp.print_full_pure_context ());
    Profile.print_profile ();
    exit 0
  end

let init_toplevel = init

let start () =
  let () = init_toplevel (List.tl (Array.to_list Sys.argv)) in
  (* In batch mode, Coqtop has already exited at this point. In interactive one,
     dump glob is nothing but garbage ...  *)
  if !Flags.ide_slave then
    Ide_slave.loop ()
  else if Flags.async_proofs_is_worker () then
    Stm.slave_main_loop ()
  else
    let () = if Dumpglob.dump () then
      let () = if_verbose warning "Dumpglob cannot be used in interactive mode." in
      Dumpglob.noglob () in
    Coqloop.loop();
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  exit 1

(* [Coqtop.start] will be called by the code produced by coqmktop *)
