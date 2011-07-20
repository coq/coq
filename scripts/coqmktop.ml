(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* coqmktop is a script to link Coq, analogous to ocamlmktop.
   The command line contains options specific to coqmktop, options for the
   Ocaml linker and files to link (in addition to the default Coq files). *)

open Unix

(* Objects to link *)

(* 1. Core objects *)
let ocamlobjs = ["str.cma";"unix.cma";"nums.cma"]
let dynobjs = ["dynlink.cma"]
let camlp4objs =
  if Coq_config.camlp4 = "camlp5" then ["gramlib.cma"] else ["camlp4lib.cma"]
let libobjs = ocamlobjs @ camlp4objs

let spaces = Str.regexp "[ \t\n]+"
let split_list l = Str.split spaces l

let copts     = split_list Tolink.copts
let core_objs = split_list Tolink.core_objs
let core_libs = split_list Tolink.core_libs

(* 3. Toplevel objects *)
let camlp4topobjs =
  if Coq_config.camlp4 = "camlp5" then
    ["camlp5_top.cma"; "pa_o.cmo"; "pa_extend.cmo"]
  else
    [ "Camlp4Top.cmo";
      "Camlp4Parsers/Camlp4OCamlRevisedParser.cmo";
      "Camlp4Parsers/Camlp4OCamlParser.cmo";
      "Camlp4Parsers/Camlp4GrammarParser.cmo";
      "q_util.cmo"; "q_coqast.cmo" ]
let topobjs = camlp4topobjs

let gramobjs = []
let notopobjs = gramobjs

(* 4. High-level tactics objects *)

(* environment *)
let opt        = ref false
let full       = ref false
let top        = ref false
let echo       = ref false

let src_dirs () =
  [ []; ["kernel";"byterun"]; [ "config" ]; [ "toplevel" ] ]

let includes () =
  let coqlib = Envars.coqlib () in
  let camlp4lib = Envars.camlp4lib () in
    List.fold_right
      (fun d l -> "-I" :: ("\"" ^ List.fold_left Filename.concat coqlib d ^ "\"") :: l)
      (src_dirs ())
      (["-I"; "\"" ^ camlp4lib ^ "\""] @
	  ["-I"; "\"" ^ coqlib ^ "\""])

(* Transform bytecode object file names in native object file names *)
let native_suffix f =
  if Filename.check_suffix f ".cmo" then
    (Filename.chop_suffix f ".cmo") ^ ".cmx"
  else if Filename.check_suffix f ".cma" then
    (Filename.chop_suffix f ".cma") ^ ".cmxa"
  else
    if Filename.check_suffix f ".a" then f
    else
      failwith ("File "^f^" has not extension .cmo, .cma or .a")

(* Transforms a file name in the corresponding Caml module name. *)
let rem_ext_regexpr = Str.regexp "\\(.*\\)\\.\\(cm..?\\|ml\\)"

let module_of_file name =
  let s = Str.replace_first rem_ext_regexpr "\\1" (Filename.basename name) in
  String.capitalize s

(* Build the list of files to link and the list of modules names *)
let files_to_link userfiles =
  let dyn_objs =
    if not !opt || Coq_config.has_natdynlink then dynobjs else [] in
  let toplevel_objs =
    if !top then topobjs else if !opt then notopobjs else [] in
  let objs = dyn_objs @ libobjs @ core_objs @ toplevel_objs in
  let modules = List.map module_of_file (objs @ userfiles)
  in
  let libs = dyn_objs @ libobjs @ core_libs @ toplevel_objs in
  let libstolink =
    (if !opt then List.map native_suffix libs else libs) @ userfiles
  in
  (modules, libstolink)

(* Gives the list of all the directories under [dir].
   Uses [Unix] (it is hard to do without it). *)
let all_subdirs dir =
  let l = ref [dir] in
  let add f = l := f :: !l in
  let rec traverse dir =
    let dirh =
      try opendir dir with Unix_error _ -> invalid_arg "all_subdirs"
    in
    try
      while true do
	let f = readdir dirh in
	if f <> "." && f <> ".." then
	  let file = Filename.concat dir f in
	  if (stat file).st_kind = S_DIR then begin
	    add file;
	    traverse file
	  end
      done
    with End_of_file ->
      closedir dirh
  in
  traverse dir; List.rev !l

(* usage *)
let usage () =
  prerr_endline "Usage: coqmktop <options> <ocaml options> files\
\nFlags are:\
\n  -coqlib dir    Specify where the Coq object files are\
\n  -camlbin dir   Specify where the OCaml binaries are\
\n  -camlp4bin dir Specify where the Camlp4/5 binaries are\
\n  -o exec-file   Specify the name of the resulting toplevel\
\n  -boot          Run in boot mode\
\n  -echo          Print calls to external commands\
\n  -full          Link high level tactics\
\n  -opt           Compile in native code\
\n  -top           Build Coq on a OCaml toplevel (incompatible with -opt)\
\n  -R dir         Add recursively dir to OCaml search path\
\n";
  exit 1

(* parsing of the command line *)
let parse_args () =
  let rec parse (op,fl) = function
    | [] -> List.rev op, List.rev fl
    | "-coqlib" :: d :: rem ->
	Flags.coqlib_spec := true; Flags.coqlib := d ; parse (op,fl) rem
    | "-coqlib" :: _        -> usage ()
    | "-camlbin" :: d :: rem ->
	Flags.camlbin_spec := true; Flags.camlbin := d ; parse (op,fl) rem
    | "-camlbin" :: _        -> usage ()
    | "-camlp4bin" :: d :: rem ->
	Flags.camlp4bin_spec := true; Flags.camlp4bin := d ; parse (op,fl) rem
    | "-camlp4bin" :: _        -> usage ()
    | "-boot" :: rem -> Flags.boot := true; parse (op,fl) rem
    | "-opt" :: rem -> opt := true ; parse (op,fl) rem
    | "-full" :: rem -> full := true ; parse (op,fl) rem
    | "-top" :: rem -> top := true ; parse (op,fl) rem
    | "-v8" :: rem ->
	Printf.eprintf "warning: option -v8 deprecated";
	parse (op,fl) rem
    | "-echo" :: rem -> echo := true ; parse (op,fl) rem
    | ("-cclib"|"-ccopt"|"-I"|"-o"|"-w" as o) :: rem' ->
	begin
	  match rem' with
	    | a :: rem -> parse (a::o::op,fl) rem
	    | []       -> usage ()
	end
    | "-R" :: a :: rem ->
        parse ((List.rev(List.flatten (List.map (fun d -> ["-I";d])
					 (all_subdirs a))))@op,fl) rem
    | "-R" :: [] -> usage ()
    | ("-noassert"|"-compact"|"-g"|"-p"|"-thread"|"-dtypes" as o) :: rem ->
        parse (o::op,fl) rem
    | ("-h"|"--help") :: _ -> usage ()
    | f :: rem ->
	if Filename.check_suffix f ".ml"
	  or Filename.check_suffix f ".cmx"
	  or Filename.check_suffix f ".cmo"
	  or Filename.check_suffix f ".cmxa"
	  or Filename.check_suffix f ".cma" then
	    parse (op,f::fl) rem
	else begin
	  prerr_endline ("Don't know what to do with " ^ f);
	  exit 1
	end
  in
  parse ([Coq_config.osdeplibs],[]) (List.tl (Array.to_list Sys.argv))

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

(* Creates another temporary file for Dynlink if needed *)
let tmp_dynlink()=
  let tmp = Filename.temp_file "coqdynlink" ".ml" in
  let _ = Sys.command ("echo \"Dynlink.init();;\" > "^tmp) in
  tmp

(* Initializes the kind of loading in the main program *)
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
\n         (fun f -> if not (Topdirs.load_file ppf f) then Util.error (\"Could not load plugin \"^f));\
\n        Mltop.use_file=Topdirs.dir_use ppf;\
\n        Mltop.add_dir=Topdirs.dir_directory;\
\n        Mltop.ml_loop=(fun () -> Toploop.loop ppf) };;\
\n"

(* create a temporary main file to link *)
let create_tmp_main_file modules =
  let main_name = Filename.temp_file "coqmain" ".ml" in
  let oc = open_out main_name in
  try
    (* Add the pre-linked modules *)
    output_string oc "List.iter Mltop.add_known_module [\"";
    output_string oc (String.concat "\";\"" modules);
    output_string oc "\"];;\n";
    (* Initializes the kind of loading *)
    output_string oc (declare_loading_string());
    (* Start the toplevel loop *)
    output_string oc "Coqtop.start();;\n";
    close_out oc;
    main_name
  with e ->
    clean main_name; raise e

(* main part *)
let main () =
  let (options, userfiles) = parse_args () in
  (* which ocaml command to invoke *)
  let camlbin = Envars.camlbin () in
  let prog =
    if !opt then begin
      (* native code *)
      if !top then failwith "no custom toplevel in native code !";
      let ocamloptexec = Filename.concat camlbin "ocamlopt" in
        ocamloptexec^" -linkall"
    end else
      (* bytecode (we shunt ocamlmktop script which fails on win32) *)
      let ocamlmktoplib = " toplevellib.cma" in
      let ocamlcexec = Filename.concat camlbin "ocamlc" in
      let ocamlccustom = Printf.sprintf "%s %s -linkall "
        ocamlcexec Coq_config.coqrunbyteflags in
      (if !top then ocamlccustom^ocamlmktoplib else ocamlccustom)
  in
  (* files to link *)
  let (modules, tolink) = files_to_link userfiles in
  (*file for dynlink *)
  let dynlink=
    if not (!opt || !top) then
      [tmp_dynlink()]
    else
      []
  in
  (* the list of the loaded modules *)
  let main_file = create_tmp_main_file modules in
  try
    let args =
      options @ (includes ()) @ copts @ tolink @ dynlink @ [ main_file ] in
      (* add topstart.cmo explicitly because we shunted ocamlmktop wrapper *)
    let args = if !top then args @ [ "topstart.cmo" ] else args in
      (* Now, with the .cma, we MUST use the -linkall option *)
    let command = String.concat " " (prog::"-rectypes"::args) in
      if !echo then
	begin
	  print_endline command;
	  print_endline
	    ("(command length is " ^
	       (string_of_int (String.length command)) ^ " characters)");
	  flush Pervasives.stdout
	end;
      let retcode = Sys.command command in
	clean main_file;
	(* command gives the exit code in HSB, and signal in LSB !!! *)
	if retcode > 255 then retcode lsr 8 else retcode
  with e ->
    clean main_file; raise e

let retcode =
  try Printexc.print main () with _ -> 1

let _ = exit retcode
