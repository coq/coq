(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open System
open Flags
open Names
open Libnames
open Nameops
open States
open Toplevel
open Coqinit

let get_version_date () =
  try
    let coqlib = Envars.coqlib () in
    let ch = open_in (Filename.concat coqlib "revision") in
    let ver = input_line ch in
    let rev = input_line ch in
      (ver,rev)
  with e when Errors.noncritical e ->
    (Coq_config.version,Coq_config.date)

let print_header () =
  let (ver,rev) = (get_version_date ()) in
    Printf.printf "Welcome to Coq %s (%s)\n" ver rev;
    flush stdout

let output_context = ref false

let memory_stat = ref false

let print_memory_stat () =
  if !memory_stat then
    Format.printf "total heap size = %d kbytes\n" (heap_size_kb ())

let _ = at_exit print_memory_stat

let engagement = ref None
let set_engagement c = engagement := Some c
let engage () =
  match !engagement with Some c -> Global.set_engagement c | None -> ()

let set_batch_mode () = batch_mode := true

let toplevel_default_name = make_dirpath [id_of_string "Top"]
let toplevel_name = ref (Some toplevel_default_name)
let set_toplevel_name dir =
  if dir = empty_dirpath then error "Need a non empty toplevel module name";
  toplevel_name := Some dir
let unset_toplevel_name () = toplevel_name := None

let remove_top_ml () = Mltop.remove ()

let inputstate = ref None
let set_inputstate s = inputstate:= Some s
let inputstate () =
  match !inputstate with
    | Some "" -> ()
    | Some s -> intern_state s
    | None -> intern_state "initial.coq"

let outputstate = ref ""
let set_outputstate s = outputstate:=s
let outputstate () = if !outputstate <> "" then extern_state !outputstate

let set_default_include d = push_include (d,Nameops.default_root_prefix)
let set_include d p =
  let p = dirpath_of_string p in
  push_include (d,p)
let set_rec_include d p =
  let p = dirpath_of_string p in
  push_rec_include(d,p)

let load_vernacular_list = ref ([] : (string * bool) list)
let add_load_vernacular verb s =
  load_vernacular_list := ((make_suffix s ".v"),verb) :: !load_vernacular_list
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

let require_list = ref ([] : string list)
let add_require s = require_list := s :: !require_list
let require () =
  List.iter (fun s -> Library.require_library_from_file None s (Some false))
    (List.rev !require_list)

let compile_list = ref ([] : (bool * string) list)
let add_compile verbose s =
  set_batch_mode ();
  Flags.make_silent true;
  compile_list := (verbose,s) :: !compile_list
let compile_files () =
  let init_state = States.freeze() in
  let coqdoc_init_state = Dumpglob.coqdoc_freeze () in
    List.iter
      (fun (v,f) ->
	 States.unfreeze init_state;
	 Dumpglob.coqdoc_unfreeze coqdoc_init_state;
	 if Flags.do_beautify () then
	   with_option beautify_file (Vernac.compile v) f
	 else
	   Vernac.compile v f)
      (List.rev !compile_list)

(*s options for the virtual machine *)

let boxed_val = ref false
let use_vm = ref false

let set_vm_opt () =
  Vm.set_transp_values (not !boxed_val);
  Vconv.set_use_vm !use_vm

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

let warning s = msg_warning (str s)

let ide_slave = ref false
let filter_opts = ref false

let verb_compat_ntn = ref false
let no_compat_ntn = ref false

let parse_args arglist =
  let glob_opt = ref false in
  let rec parse = function
    | [] -> []
    | "-with-geoproof" :: s :: rem ->
	if s = "yes" then Coq_config.with_geoproof := true
	else if s = "no" then Coq_config.with_geoproof := false
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
    | "-outputstate" :: s :: rem ->
      Flags.load_proofs := Flags.Force; set_outputstate s; parse rem
    | "-outputstate" :: []       -> usage ()

    | "-nois" :: rem -> set_inputstate ""; parse rem

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

    | "-compile" :: f :: rem -> add_compile false f; if not !glob_opt then Dumpglob.dump_to_dotglob (); parse rem
    | "-compile" :: []       -> usage ()

    | "-compile-verbose" :: f :: rem -> add_compile true f;  if not !glob_opt then Dumpglob.dump_to_dotglob (); parse rem
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
	parse rem
    | "-emacs-U" :: rem ->
	warning "Obsolete option \"-emacs-U\", use -emacs instead.";	
	parse ("-emacs" :: rem)

    | "-unicode" :: rem -> add_require "Utf8_core"; parse rem

    | "-coqlib" :: d :: rem -> Flags.coqlib_spec:=true; Flags.coqlib:=d; parse rem
    | "-coqlib" :: [] -> usage ()

    | "-where" :: _ -> print_endline (Envars.coqlib ()); exit (if !filter_opts then 2 else 0)

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

    | "-no-hash-consing" :: rem -> Flags.hash_cons_proofs := false; parse rem

    | "-ideslave" :: rem -> ide_slave := true; parse rem

    | "-filteropts" :: rem -> filter_opts := true; parse rem

    | s :: rem ->
      if !filter_opts then
       s :: (parse rem)
      else
       (prerr_endline ("Don't know what to do with " ^ s); usage ())
  in
  try
    parse arglist
  with
    | UserError(_,s) as e -> begin
	try
	  Stream.empty s; exit 1
	with Stream.Failure ->
	  msgnl (Errors.print e); exit 1
      end
    | any -> begin msgnl (Errors.print any); exit 1 end

let init arglist =
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init();
  (* Default Proofb Mode starts with an alternative default. *)
  Goptions.set_string_option_value ["Default";"Proof";"Mode"] "Classic";
  begin
    try
      let foreign_args = parse_args arglist in
      if !filter_opts then
        (print_string (String.concat "\n" foreign_args); exit 0);
      if !ide_slave then begin
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
      if (not !batch_mode|| !compile_list=[]) && Global.env_is_empty() then
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
      if not !batch_mode then message "Error during initialization:";
      msgnl (Toplevel.print_toplevel_error any);
      exit 1
  end;
  if !batch_mode then
    (flush_all();
     if !output_context then
       Pp.ppnl (with_option raw_print Prettyp.print_full_pure_context ());
     Profile.print_profile ();
     exit 0);
  (* We initialize the command history stack with a first entry *)
  Backtrack.mark_command Vernacexpr.VernacNop

let init_toplevel = init

let start () =
  init_toplevel (List.tl (Array.to_list Sys.argv));
  if !ide_slave then
    Ide_slave.loop ()
  else
    Toplevel.loop();
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  exit 1

(* [Coqtop.start] will be called by the code produced by coqmktop *)
