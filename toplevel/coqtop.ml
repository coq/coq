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

let fatal_error info =
  pperrnl info; flush_all (); exit 1

let get_version_date () =
  try
    let coqlib = Envars.coqlib ~fail:Errors.error in
    let ch = open_in (Filename.concat coqlib "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
      (ver,rev)
  with e when Errors.noncritical e ->
    (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = (get_version_date ()) in
  pp (str "Welcome to Coq "++ str ver ++ str " (" ++ str rev ++ str ")" ++ fnl ());
  pp_flush ()

let output_context = ref false

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then
    pp (str "total heap size = " ++ int (CObj.heap_size_kb ()) ++ str " kbytes" ++ fnl ())

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

let set_default_include d = push_include (d,Nameops.default_root_prefix)
let set_include d p =
  let p = dirpath_of_string p in
  push_include (d,p)
let set_rec_include d p =
  let p = dirpath_of_string p in
  push_rec_include(d,p)

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

let load_init = ref true

let require_prelude () =
  let q = qualid_of_string "Coq.Init.Prelude" in
  Library.require_library [Loc.ghost,q] (Some true)

let require_list = ref ([] : string list)
let add_require s = require_list := s :: !require_list
let require () =
  if !load_init then silently require_prelude ();
  List.iter (fun s -> Library.require_library_from_file None s (Some false))
    (List.rev !require_list)

let compile_list = ref ([] : (bool * string) list)

let add_compile verbose glob_opt s =
  set_batch_mode ();
  Flags.make_silent true;
  if not glob_opt then Dumpglob.dump_to_dotglob ();
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
      let init_state = States.freeze ~marshallable:false in
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

let warning s = msg_warning (strbrk s)

let filter_opts = ref false

let verb_compat_ntn = ref false
let no_compat_ntn = ref false

let parse_args arglist =
  let glob_opt = ref false in
  let rec parse = function
    | [] -> []
    | "-with-geoproof" :: s :: rem ->
	if String.equal s "yes" then Coq_config.with_geoproof := true
	else if String.equal s "no" then Coq_config.with_geoproof := false
	else usage ();
	parse rem
    | "-impredicative-set" :: rem ->
        set_engagement Declarations.ImpredicativeSet; parse rem

    | ("-I"|"-include") :: d :: "-as" :: p :: rem -> set_include d p; parse rem
    | ("-I"|"-include") :: d :: "-as" :: [] -> usage ()
    | ("-I"|"-include") :: d :: rem -> set_default_include d; parse rem
    | ("-I"|"-include") :: []       -> usage ()

    | "-R" :: d :: "-as" :: p :: rem -> set_rec_include d p;parse rem
    | "-R" :: d :: "-as" :: [] -> usage ()
    | "-R" :: d :: p :: rem -> set_rec_include d p;parse rem
    | "-R" :: ([] | [_]) -> usage ()

    | "-top" :: d :: rem -> set_toplevel_name (dirpath_of_string d); parse rem
    | "-top" :: [] -> usage ()

    | "-exclude-dir" :: f :: rem -> exclude_search_in_dirname f; parse rem
    | "-exclude-dir" :: [] -> usage ()

    | "-notop" :: rem -> unset_toplevel_name (); parse rem
    | "-q" :: rem -> no_load_rc (); parse rem

    | "-opt" :: rem -> warning "option -opt deprecated, call with .opt suffix\n"; parse rem
    | "-byte" :: rem -> warning "option -byte deprecated, call with .byte suffix\n"; parse rem
    | "-full" :: rem -> warning "option -full deprecated\n"; parse rem

    | "-batch" :: rem -> set_batch_mode (); parse rem
    | "-boot" :: rem -> boot := true; no_load_rc (); parse rem
    | "-quality" :: rem -> term_quality := true; no_load_rc (); parse rem
    | "-outputstate" :: s :: rem -> set_outputstate s; parse rem
    | "-outputstate" :: []       -> usage ()

    | ("-noinit"|"-nois") :: rem -> load_init := false; parse rem

    | ("-inputstate"|"-is") :: s :: rem -> set_inputstate s; parse rem
    | ("-inputstate"|"-is") :: []       -> usage ()

    | "-load-ml-object" :: f :: rem -> Mltop.dir_ml_load f; parse rem
    | "-load-ml-object" :: []       -> usage ()

    | "-load-ml-source" :: f :: rem -> Mltop.dir_ml_use f; parse rem
    | "-load-ml-source" :: []       -> usage ()

    | ("-load-vernac-source"|"-l") :: f :: rem ->
	add_load_vernacular false f; parse rem
    | ("-load-vernac-source"|"-l") :: []       -> usage ()

    | ("-load-vernac-source-verbose"|"-lv") :: f :: rem ->
	add_load_vernacular true f; parse rem
    | ("-load-vernac-source-verbose"|"-lv") :: []       -> usage ()

    | "-load-vernac-object" :: f :: rem -> add_vernac_obj f; parse rem
    | "-load-vernac-object" :: []       -> usage ()

    | "-dump-glob" :: "stdout" :: rem -> Dumpglob.dump_to_stdout (); glob_opt := true; parse rem
	  (* À ne pas documenter : l'option 'stdout' n'étant
	     éventuellement utile que pour le debugging... *)
    | "-dump-glob" :: f :: rem -> Dumpglob.dump_into_file f; glob_opt := true; parse rem
    | "-dump-glob" :: []       -> usage ()
    | ("-no-glob" | "-noglob") :: rem -> Dumpglob.noglob (); glob_opt := true; parse rem

    | "-require" :: f :: rem -> add_require f; parse rem
    | "-require" :: []       -> usage ()

    | "-print-mod-uid" :: f :: rem -> Flags.print_mod_uid := true;
                                      add_require f; parse rem

    | "-compile" :: f :: rem -> add_compile false !glob_opt f; parse rem
    | "-compile" :: []       -> usage ()

    | "-compile-verbose" :: f :: rem -> add_compile true !glob_opt f; parse rem
    | "-compile-verbose" :: []       -> usage ()

    | "-force-load-proofs" :: rem -> Flags.load_proofs := Flags.Force; parse rem
    | "-lazy-load-proofs" :: rem -> Flags.load_proofs := Flags.Lazy; parse rem
    | "-dont-load-proofs" :: rem -> Flags.load_proofs := Flags.Dont; parse rem

    | "-beautify" :: rem -> make_beautify true; parse rem

    | "-unsafe" :: f :: rem -> add_unsafe f; parse rem
    | "-unsafe" :: []       -> usage ()

    | "-debug" :: rem -> set_debug (); parse rem

    | "-time" :: rem -> Vernac.time := true; parse rem

    | "-compat" :: v :: rem ->
        Flags.compat_version := get_compat_version v; parse rem
    | "-compat" :: []       -> usage ()

    | "-verbose-compat-notations" :: rem -> verb_compat_ntn := true; parse rem
    | "-no-compat-notations" :: rem -> no_compat_ntn := true; parse rem

    | "-vm" :: rem -> use_vm := true; parse rem
    | "-emacs" :: rem ->
	Flags.print_emacs := true; Pp.make_pp_emacs();
	Vernacentries.qed_display_script := false;
        Flags.make_term_color false;
	parse rem
    | "-emacs-U" :: rem ->
	warning "Obsolete option \"-emacs-U\", use -emacs instead.";	
        Flags.make_term_color false;
	parse ("-emacs" :: rem)

    | "-unicode" :: rem -> add_require "Utf8_core"; parse rem

    | "-coqlib" :: d :: rem -> Flags.coqlib_spec:=true; Flags.coqlib:=d; parse rem
    | "-coqlib" :: [] -> usage ()

    | "-where" :: _ ->
        print_endline (Envars.coqlib ~fail:Errors.error);
        exit (if !filter_opts then 2 else 0)

    | ("-config"|"--config") :: _ -> Usage.print_config (); exit (if !filter_opts then 2 else 0)

    | ("-quiet"|"-silent") :: rem -> Flags.make_silent true; parse rem

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> Usage.version (if !filter_opts then 2 else 0)

    | "-init-file" :: f :: rem -> set_rcfile f; parse rem
    | "-init-file" :: []       -> usage ()

    | "-notactics" :: rem ->
	warning "Obsolete option \"-notactics\".";
	remove_top_ml (); parse rem

    | "-just-parsing" :: rem -> Vernac.just_parsing := true; parse rem

    | ("-m" | "--memory") :: rem -> memory_stat := true; parse rem

    | "-xml" :: rem -> Flags.xml_export := true; parse rem

    | "-output-context" :: rem -> output_context := true; parse rem

    (* Scanned in Flags. *)
    | "-v7" :: rem -> error "This version of Coq does not support v7 syntax"
    | "-v8" :: rem -> parse rem

    | "-ideslave" :: rem -> Flags.ide_slave := true; parse rem

    | "-filteropts" :: rem -> filter_opts := true; parse rem

    | "-color" :: rem -> Flags.make_term_color true; parse rem

    | "-no-native-compiler" :: rem -> no_native_compiler := true; parse rem

    | s :: rem ->
      if !filter_opts then
       s :: (parse rem)
      else
       (prerr_endline ("Don't know what to do with " ^ s); usage ())
  in
  try
    parse arglist
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
      let foreign_args = parse_args arglist in
      if !filter_opts then
        (print_string (String.concat "\n" foreign_args); exit 0);
      if !Flags.ide_slave then begin
        Flags.make_silent true;
        Ide_slave.init_stdout ()
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
      if (not !batch_mode|| List.is_empty !compile_list) && Global.env_is_empty() then
        Option.iter Declaremods.start_library !toplevel_name;
      init_library_roots ();
      load_vernac_obj ();
      require ();
      load_rcfile();
      load_vernacular ();
      compile_files ();
      outputstate ()
    with any ->
      flush_all();
      let msg =
        if !batch_mode then mt ()
        else str "Error during initialization:" ++ fnl ()
      in
      fatal_error (msg ++ Toplevel.print_toplevel_error any)
  end;
  if !batch_mode then begin
    flush_all();
    if !output_context then
      Pp.ppnl (with_option raw_print Prettyp.print_full_pure_context ());
    Profile.print_profile ();
    exit 0
  end;
  (* We initialize the command history stack with a first entry *)
  Backtrack.mark_command Vernacexpr.VernacNop

let init_toplevel = init

let start () =
  let () = init_toplevel (List.tl (Array.to_list Sys.argv)) in
  (* In batch mode, Coqtop has already exited at this point. In interactive one,
     dump glob is nothing but garbage ...  *)
  let () = if Dumpglob.dump () then
    let () = if_verbose warning "Dumpglob cannot be used in interactive mode." in
    Dumpglob.noglob () in
  if !Flags.ide_slave then
    Ide_slave.loop ()
  else
    Toplevel.loop();
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  exit 1

(* [Coqtop.start] will be called by the code produced by coqmktop *)
