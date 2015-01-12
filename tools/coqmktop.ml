(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {1 Coqmktop} *)

(** coqmktop is a script to link Coq, analogous to ocamlmktop.
   The command line contains options specific to coqmktop, options for the
   Ocaml linker and files to link (in addition to the default Coq files). *)

(** {6 Utilities} *)

(** Split a string at each blank
*)
let split_list =
  let spaces = Str.regexp "[ \t\n]+" in
  fun str -> Str.split spaces str

let (/) = Filename.concat

(** Which user files do we support (and propagate to ocamlopt) ?
*)
let supported_suffix f = match CUnix.get_extension f with
  | ".ml" | ".cmx" | ".cmo" | ".cmxa" | ".cma" | ".c" -> true
  | _ -> false

(** From bytecode extension to native
*)
let native_suffix f = match CUnix.get_extension f with
  | ".cmo" -> (Filename.chop_suffix f ".cmo") ^ ".cmx"
  | ".cma" -> (Filename.chop_suffix f ".cma") ^ ".cmxa"
  | ".a" -> f
  | _ -> failwith ("File "^f^" has not extension .cmo, .cma or .a")

(** Transforms a file name in the corresponding Caml module name.
*)
let module_of_file name =
  String.capitalize
    (try Filename.chop_extension name with Invalid_argument _ -> name)

(** Run a command [prog] with arguments [args].
    We do not use [Sys.command] anymore, see comment in [CUnix.sys_command].
*)
let run_command prog args =
  match CUnix.sys_command prog args with
  | Unix.WEXITED 127 -> failwith ("no such command "^prog)
  | Unix.WEXITED n -> n
  | Unix.WSIGNALED n -> failwith (prog^" killed by signal "^string_of_int n)
  | Unix.WSTOPPED n -> failwith (prog^" stopped by signal "^string_of_int n)



(** {6 Coqmktop options} *)

let opt        = ref false
let top        = ref false
let echo       = ref false
let no_start   = ref false

let is_ocaml4 = Coq_config.caml_version.[0] <> '3'
let is_camlp5 = Coq_config.camlp4 = "camlp5"


(** {6 Includes options} *)

(** Since the Coq core .cma are given with their relative paths
    (e.g. "lib/clib.cma"), we only need to include directories mentionned in
    the temp main ml file below (for accessing the corresponding .cmi). *)

let std_includes basedir =
  let rebase d = match basedir with None -> d | Some base -> base / d in
  ["-I"; rebase ".";
   "-I"; rebase "lib";
   "-I"; rebase "toplevel";
   "-I"; rebase "kernel/byterun";
   "-I"; Envars.camlp4lib () ] @
  (if is_ocaml4 then ["-I"; "+compiler-libs"] else [])

(** For the -R option, visit all directories under [dir] and add
    corresponding -I to the [opts] option list (in reversed order) *)
let incl_all_subdirs dir opts =
  let l = ref opts in
  let add f = l := f :: "-I" :: !l in
  let rec traverse dir =
    if Sys.file_exists dir && Sys.is_directory dir then
      let () = add dir in
      let subdirs = try Sys.readdir dir with any -> [||] in
      Array.iter (fun f -> traverse (dir/f)) subdirs
  in
  traverse dir; !l


(** {6 Objects to link} *)

(** NB: dynlink is now always linked, it is used for loading plugins
    and compiled vm code (see native-compiler). We now reject platforms
    with ocamlopt but no dynlink.cmxa during ./configure, and give
    instructions there about how to build a dummy dynlink.cmxa,
    cf. dev/dynlink.ml. *)

(** OCaml + CamlpX libraries *)

let ocaml_libs = ["str.cma";"unix.cma";"nums.cma";"dynlink.cma";"threads.cma"]
let camlp4_libs = if is_camlp5 then ["gramlib.cma"] else ["camlp4lib.cma"]
let libobjs = ocaml_libs @ camlp4_libs

(** Toplevel objects *)

let ocaml_topobjs =
  if is_ocaml4 then
    ["ocamlcommon.cma";"ocamlbytecomp.cma";"ocamltoplevel.cma"]
  else
    ["toplevellib.cma"]

let camlp4_topobjs =
  if is_camlp5 then
    ["camlp5_top.cma"; "pa_o.cmo"; "pa_extend.cmo"]
  else
    [ "Camlp4Top.cmo";
      "Camlp4Parsers/Camlp4OCamlRevisedParser.cmo";
      "Camlp4Parsers/Camlp4OCamlParser.cmo";
      "Camlp4Parsers/Camlp4GrammarParser.cmo" ]

let topobjs = ocaml_topobjs @ camlp4_topobjs

(** Coq Core objects *)

let copts = (split_list Coq_config.osdeplibs) @ (split_list Tolink.copts)
let core_objs = split_list Tolink.core_objs
let core_libs = split_list Tolink.core_libs

(** Build the list of files to link and the list of modules names
*)
let files_to_link userfiles =
  let top = if !top then topobjs else [] in
  let modules = List.map module_of_file (top @ core_objs @ userfiles) in
  let objs = libobjs @ top @ core_libs in
  let objs' = (if !opt then List.map native_suffix objs else objs) @ userfiles
  in (modules, objs')


(** {6 Parsing of the command-line} *)

let usage () =
  prerr_endline "Usage: coqmktop <options> <ocaml options> files\
\nFlags are:\
\n  -coqlib dir    Specify where the Coq object files are\
\n  -camlbin dir   Specify where the OCaml binaries are\
\n  -camlp4bin dir Specify where the Camlp4/5 binaries are\
\n  -o exec-file   Specify the name of the resulting toplevel\
\n  -boot          Run in boot mode\
\n  -echo          Print calls to external commands\
\n  -opt           Compile in native code\
\n  -top           Build Coq on a OCaml toplevel (incompatible with -opt)\
\n  -R dir         Add recursively dir to OCaml search path\
\n";
  exit 1

let parse_args () =
  let rec parse (op,fl) = function
    | [] -> List.rev op, List.rev fl

    (* Directories *)
    | "-coqlib" :: d :: rem ->
	Flags.coqlib_spec := true; Flags.coqlib := d ; parse (op,fl) rem
    | "-camlbin" :: d :: rem ->
	Flags.camlbin_spec := true; Flags.camlbin := d ; parse (op,fl) rem
    | "-camlp4bin" :: d :: rem ->
	Flags.camlp4bin_spec := true; Flags.camlp4bin := d ; parse (op,fl) rem
    | "-R" :: d :: rem -> parse (incl_all_subdirs d op,fl) rem
    | ("-coqlib"|"-camlbin"|"-camlp4bin"|"-R") :: [] -> usage ()

    (* Boolean options of coqmktop *)
    | "-boot" :: rem -> Flags.boot := true; parse (op,fl) rem
    | "-opt" :: rem -> opt := true ; parse (op,fl) rem
    | "-top" :: rem -> top := true ; parse (op,fl) rem
    | "-no-start" :: rem -> no_start:=true; parse (op, fl) rem
    | "-echo" :: rem -> echo := true ; parse (op,fl) rem
    | ("-v8"|"-full" as o) :: rem ->
	Printf.eprintf "warning: option %s deprecated\n" o; parse (op,fl) rem

    (* Extra options with arity 0 or 1, directly passed to ocamlc/ocamlopt *)
    | ("-noassert"|"-compact"|"-g"|"-p"|"-thread"|"-dtypes" as o) :: rem ->
        parse (o::op,fl) rem
    | ("-cclib"|"-ccopt"|"-I"|"-o"|"-w" as o) :: rem' ->
	begin
	  match rem' with
	    | a :: rem -> parse (a::o::op,fl) rem
	    | []       -> usage ()
	end

    | ("-h"|"-help"|"--help") :: _ -> usage ()
    | f :: rem when supported_suffix f -> parse (op,f::fl) rem
    | f :: _ -> prerr_endline ("Don't know what to do with " ^ f); exit 1
  in
  parse ([],[]) (List.tl (Array.to_list Sys.argv))


(** {6 Temporary main file} *)

(** remove the temporary main file
*)
let clean file =
  let rm f = if Sys.file_exists f then Sys.remove f in
  let basename = Filename.chop_suffix file ".ml" in
  if not !echo then begin
    rm file;
    rm (basename ^ ".o");
    rm (basename ^ ".cmi");
    rm (basename ^ ".cmo");
    rm (basename ^ ".cmx")
  end

(** Initializes the kind of loading in the main program
*)
let declare_loading_string () =
  if not !top then
    "Mltop.remove ();;"
  else
    "begin try\
\n       (* Enable rectypes in the toplevel if it has the directive #rectypes *)\
\n       begin match Hashtbl.find Toploop.directive_table \"rectypes\" with\
\n         | Toploop.Directive_none f -> f ()\
\n         | _ -> ()\
\n       end\
\n     with\
\n       | Not_found -> ()\
\n     end;;\
\n\
\n     let ppf = Format.std_formatter;;\
\n     Mltop.set_top\
\n       {Mltop.load_obj=\
\n         (fun f -> if not (Topdirs.load_file ppf f)\
\n                   then Errors.error (\"Could not load plugin \"^f));\
\n        Mltop.use_file=Topdirs.dir_use ppf;\
\n        Mltop.add_dir=Topdirs.dir_directory;\
\n        Mltop.ml_loop=(fun () -> Toploop.loop ppf) };;\
\n"

(** create a temporary main file to link
*)
let create_tmp_main_file modules =
  let main_name,oc = Filename.open_temp_file "coqmain" ".ml" in
  try
    (* Add the pre-linked modules *)
    output_string oc "List.iter Mltop.add_known_module [\"";
    output_string oc (String.concat "\";\"" modules);
    output_string oc "\"];;\n";
    (* Initializes the kind of loading *)
    output_string oc (declare_loading_string());
    (* Start the toplevel loop *)
    if not !no_start then output_string oc "Coqtop.start();;\n";
    close_out oc;
    main_name
  with reraise ->
    clean main_name; raise reraise


(** {6 Main } *)

let main () =
  let (options, userfiles) = parse_args () in
  (* Directories: *)
  let () = Envars.set_coqlib ~fail:Errors.error in
  let camlbin = Envars.camlbin () in
  let basedir = if !Flags.boot then None else Some (Envars.coqlib ()) in
  (* Which ocaml compiler to invoke *)
  let prog = camlbin/(if !opt then "ocamlopt" else "ocamlc") in
  (* Which arguments ? *)
  if !opt && !top then failwith "no custom toplevel in native code !";
  let flags = if !opt then [] else Coq_config.vmbyteflags in
  let topstart = if !top then [ "topstart.cmo" ] else [] in
  let (modules, tolink) = files_to_link userfiles in
  let main_file = create_tmp_main_file modules in
  try
    (* - We add topstart.cmo explicitly because we shunted ocamlmktop wrapper.
       - With the coq .cma, we MUST use the -linkall option. *)
    let args =
      "-linkall" :: "-rectypes" :: flags @ copts @ options @
      (std_includes basedir) @ tolink @ [ main_file ] @ topstart
    in
    if !echo then begin
      let command = String.concat " " (prog::args) in
      print_endline command;
      print_endline
	("(command length is " ^
	    (string_of_int (String.length command)) ^ " characters)");
      flush Pervasives.stdout
    end;
    let exitcode = run_command prog args in
    clean main_file;
    exitcode
  with reraise -> clean main_file; raise reraise

let pr_exn = function
  | Failure msg -> msg
  | Unix.Unix_error (err,fn,arg) -> fn^" "^arg^" : "^Unix.error_message err
  | any -> Printexc.to_string any

let _ =
  try exit (main ())
  with any -> Printf.eprintf "Error: %s\n" (pr_exn any); exit 1
