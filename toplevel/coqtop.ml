(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
  with _ -> (Coq_config.version,Coq_config.date)

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

let re_exec_version = ref ""
let set_byte () = re_exec_version := "byte"
let set_opt () = re_exec_version := "opt"

(* Re-exec Coq in bytecode or native code if necessary. [s] is either
   ["byte"] or ["opt"]. Notice that this is possible since the nature of
   the toplevel has already been set in [Mltop] by the main file created
   by coqmktop (see scripts/coqmktop.ml). *)

let re_exec is_ide =
  let s = !re_exec_version in
  let is_native = Mltop.is_native in
  (* Unix.readlink is not implemented on Windows architectures :-(
     let prog =
       try Unix.readlink "/proc/self/exe"
       with Unix.Unix_error _ -> Sys.argv.(0) in
  *)
  let prog = Sys.argv.(0) in
  if (is_native && s = "byte") || ((not is_native) && s = "opt")
  then begin
    let s = if s = "" then if is_native then "opt" else "byte" else s in
    let newprog =
      let dir = Filename.dirname prog in
      let coqtop = if is_ide then "coqide." else "coqtop." in
      let com = coqtop ^ s ^ Coq_config.exec_extension in
      if dir <> "." then Filename.concat dir com else com
    in
    Sys.argv.(0) <- newprog;
    Unix.handle_unix_error (Unix.execvp newprog) Sys.argv
  end

(*s options for the virtual machine *)

let boxed_val = ref false
let boxed_def = ref false
let use_vm = ref false

let set_vm_opt () =
  Vm.set_transp_values (not !boxed_val);
  Flags.set_boxed_definitions !boxed_def;
  Vconv.set_use_vm !use_vm

(*s Compatibility options *)

let compat_version = ref None
let set_compat_options () =
  Option.iter Coqcompat.set_compat_options !compat_version

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


let ide_args = ref []
let parse_args is_ide =
  let glob_opt = ref false in
  let rec parse = function
    | [] -> ()
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

    | "-opt" :: rem -> set_opt(); parse rem
    | "-byte" :: rem -> set_byte(); parse rem
    | "-full" :: rem -> warning "option -full deprecated\n"; parse rem

    | "-batch" :: rem -> set_batch_mode (); parse rem
    | "-boot" :: rem -> boot := true; no_load_rc (); parse rem
    | "-quality" :: rem -> term_quality := true; no_load_rc (); parse rem
    | "-outputstate" :: s :: rem -> set_outputstate s; parse rem
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

    | "-dont-load-proofs" :: rem -> Flags.dont_load_proofs := true; parse rem

    | "-beautify" :: rem -> make_beautify true; parse rem

    | "-unsafe" :: f :: rem -> add_unsafe f; parse rem
    | "-unsafe" :: []       -> usage ()

    | "-debug" :: rem -> set_debug (); parse rem

    | "-compat" :: v :: rem -> compat_version := Some v; parse rem
    | "-compat" :: []       -> usage ()

    | "-vm" :: rem -> use_vm := true; parse rem
    | "-emacs" :: rem -> Flags.print_emacs := true; Pp.make_pp_emacs(); parse rem
    | "-emacs-U" :: rem -> Flags.print_emacs := true;
	Flags.print_emacs_safechar := true; Pp.make_pp_emacs(); parse rem

    | "-unicode" :: rem -> Flags.unicode_syntax := true; parse rem

    | "-coqlib" :: d :: rem -> Flags.coqlib_spec:=true; Flags.coqlib:=d; parse rem
    | "-coqlib" :: [] -> usage ()

    | "-where" :: _ -> print_endline (Envars.coqlib ()); exit 0

    | ("-config"|"--config") :: _ -> Usage.print_config (); exit 0

    | ("-quiet"|"-silent") :: rem -> Flags.make_silent true; parse rem

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> Usage.version ()

    | "-init-file" :: f :: rem -> set_rcfile f; parse rem
    | "-init-file" :: []       -> usage ()

    | "-user" :: u :: rem -> set_rcuser u; parse rem
    | "-user" :: []       -> usage ()

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

    | s :: rem ->
	if is_ide then begin
	  ide_args := s :: !ide_args;
	  parse rem
	end else begin
	  prerr_endline ("Don't know what to do with " ^ s); usage ()
	end
  in
  try
    parse (List.tl (Array.to_list Sys.argv))
  with
    | UserError(_,s) as e -> begin
	try
	  Stream.empty s; exit 1
	with Stream.Failure ->
	  msgnl (Cerrors.explain_exn e); exit 1
      end
    | e -> begin msgnl (Cerrors.explain_exn e); exit 1 end

let init is_ide =
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init();
  begin
    try
      parse_args is_ide;
      re_exec is_ide;
      if_verbose print_header ();
      init_load_path ();
      inputstate ();
      set_vm_opt ();
      set_compat_options ();
      engage ();
      if (not !batch_mode|| !compile_list=[]) && Global.env_is_empty() then
        Option.iter Declaremods.start_library !toplevel_name;
      init_library_roots ();
      load_vernac_obj ();
      require ();
      load_rcfile();
      load_vernacular ();
      compile_files ();
      outputstate ()
    with e ->
      flush_all();
      if not !batch_mode then message "Error during initialization:";
      msgnl (Toplevel.print_toplevel_error e);
      exit 1
  end;
  if !batch_mode then
    (flush_all();
     if !output_context then
       Pp.ppnl (with_option raw_print Prettyp.print_full_pure_context ());
     Profile.print_profile ();
     exit 0);
  Lib.declare_initial_state ()

let init_ide () = init true; List.rev !ide_args

let start () =
  init false;
  Toplevel.loop();
  (* Initialise and launch the Ocaml toplevel *)
  Coqinit.init_ocaml_path();
  Mltop.ocaml_toploop();
  exit 1

(* [Coqtop.start] will be called by the code produced by coqmktop *)
