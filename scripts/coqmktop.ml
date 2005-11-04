(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* coqmktop is a script to link Coq, analogous to ocamlmktop.
   The command line contains options specific to coqmktop, options for the
   Ocaml linker and files to link (in addition to the default Coq files). *)

open Unix

(* Objects to link *)

(* 1. Core objects *)
let ocamlobjs = ["unix.cma"]
let dynobjs = ["dynlink.cma"]
let camlp4objs = [(*"odyl.cma"; "camlp4.cma";*) "gramlib.cma"]
let configobjs = ["coq_config.cmo"]
let libobjs = ocamlobjs @ camlp4objs @ configobjs

let spaces = Str.regexp "[ \t\n]+"
let split_cmo l = Str.split spaces l

let lib = split_cmo Tolink.lib 
let kernel = split_cmo Tolink.kernel
let library = split_cmo Tolink.library 
let pretyping = split_cmo Tolink.pretyping 
let interp = split_cmo Tolink.interp
let parsing = split_cmo Tolink.parsing 
let proofs = split_cmo Tolink.proofs 
let tactics = split_cmo Tolink.tactics 
let toplevel = split_cmo Tolink.toplevel 
let highparsing = split_cmo Tolink.highparsing 
let highparsingnew = split_cmo Tolink.highparsingnew
let ide = split_cmo Tolink.ide 

let core_objs = 
  libobjs @ lib @ kernel @ library @ pretyping @ interp @ parsing @ 
  proofs @ tactics

let core_libs = 
  libobjs @ [ "lib/lib.cma" ; "kernel/kernel.cma" ; "library/library.cma" ;
  "pretyping/pretyping.cma" ; "interp/interp.cma" ; "parsing/parsing.cma" ;
  "proofs/proofs.cma" ; "tactics/tactics.cma" ]

(* 3. Files only in coqsearchisos (if option -searchisos is used) *)
let coqsearch = ["version_searchisos.cmo"; "cmd_searchisos_line.cmo"]

(* 4. Toplevel objects *)
let camlp4objs =
  ["camlp4_top.cma"; "pa_o.cmo"; "pa_op.cmo"; "pa_extend.cmo"; "q_util.cmo"; "q_coqast.cmo" ]
let topobjs = camlp4objs

let gramobjs = []
let notopobjs = gramobjs

(* 5. High-level tactics objects *)
let hightactics = 
 (split_cmo Tolink.hightactics) @ (split_cmo Tolink.contrib) 

(* environment *)
let src_coqtop = ref Coq_config.coqtop
let opt        = ref false
let full       = ref false
let top        = ref false
let searchisos = ref false
let coqide     = ref false
let echo       = ref false

let src_dirs () = 
  [ []; [ "config" ]; [ "toplevel" ] ] @
  if !coqide then [[ "ide" ]] else []

let includes () = 
  List.fold_right
    (fun d l -> "-I" :: List.fold_left Filename.concat !src_coqtop d :: l)
    (src_dirs ())
    (["-I"; Coq_config.camlp4lib] @ 
     (if !coqide then ["-thread"; "-I"; "+lablgtk2"] else []))

(* Transform bytecode object file names in native object file names *)
let native_suffix f =
  if Filename.check_suffix f ".cmo" then 
    (Filename.chop_suffix f ".cmo") ^ ".cmx"
  else if Filename.check_suffix f ".cma" then 
    (Filename.chop_suffix f ".cma") ^ ".cmxa"
  else 
    failwith ("File "^f^" has not extension .cmo or .cma")

(* Transforms a file name in the corresponding Caml module name. *)
let rem_ext_regexpr = Str.regexp "\\(.*\\)\\.\\(cm..?\\|ml\\)"

let module_of_file name =
  let s = Str.replace_first rem_ext_regexpr "\\1" (Filename.basename name) in
  String.capitalize s

(* Build the list of files to link and the list of modules names *)
let files_to_link userfiles =
  let dyn_objs = if not !opt then dynobjs else [] in
  let command_objs = if !searchisos then coqsearch else [] in
  let toplevel_objs =
    if !top then topobjs else if !opt then notopobjs else [] in
  let ide_objs = if !coqide then 
    "str.cma"::"threads.cma"::"lablgtk.cma"::"gtkThread.cmo"::ide 
  else [] 
  in
  let ide_libs = if !coqide then 
    ["str.cma" ; "threads.cma" ; "lablgtk.cma" ; "gtkThread.cmo" ;
     "ide/ide.cma" ]
  else [] 
  in
  let objs = 
    core_objs @ dyn_objs @ toplevel @ highparsing @ highparsingnew @ 
    command_objs @ hightactics @ toplevel_objs @ ide_objs
  and libs =
    core_libs @ dyn_objs @ 
    [ "toplevel/toplevel.cma" ; "parsing/highparsing.cma" ;
      "parsing/highparsingnew.cma" ] @ 
    command_objs @ [ "tactics/hightactics.cma" ; "contrib/contrib.cma" ] @
    toplevel_objs @ 
    ide_libs      
  in
  let objstolink,libstolink =
    if !opt then 
      ((List.map native_suffix objs) @ userfiles,
       (List.map native_suffix libs) @ userfiles)
    else 
      (objs @ userfiles ,libs @ userfiles )
  in
  let modules = List.map module_of_file objstolink in
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
  prerr_endline "Usage: coqmktop <options> <ocaml options> files
Options are:
  -srcdir dir   Specify where the Coq source files are
  -o exec-file  Specify the name of the resulting toplevel
  -opt          Compile in native code
  -full         Link high level tactics
  -top          Build Coq on a ocaml toplevel (incompatible with -opt)
  -searchisos   Build a toplevel for SearchIsos
  -ide          Build a toplevel for the Coq IDE
  -R dir        Specify recursively directories for Ocaml
  -v8           Link with V8 grammar\n";
  exit 1

(* parsing of the command line *)
let parse_args () =
  let rec parse (op,fl) = function
    | [] -> List.rev op, List.rev fl
    | "-srcdir" :: d :: rem -> src_coqtop := d ; parse (op,fl) rem
    | "-srcdir" :: _        -> usage ()
    | "-opt" :: rem -> opt := true ; parse (op,fl) rem
    | "-full" :: rem -> full := true ; parse (op,fl) rem
    | "-top" :: rem -> top := true ; parse (op,fl) rem
    | "-searchisos" :: rem ->
        searchisos := true; parse (op,fl) rem
    | "-ide" :: rem ->
        coqide := true; parse (op,fl) rem
    | "-v8" :: rem -> parse (op,fl) rem
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
    | ("-compact"|"-g"|"-p"|"-thread" as o) :: rem -> parse (o::op,fl) rem
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

(* Gives all modules in [dir]. Uses [.cmi] suffixes. Uses [Unix]. *)
let all_modules_in_dir dir =
  try
    let lst = ref []
    and stg = ref ""
    and dh = Unix.opendir dir in
    try
      while true do
	let stg = Unix.readdir dh in
        if (Filename.check_suffix stg ".cmi") then
          lst := !lst @ [String.capitalize (Filename.chop_suffix stg ".cmi")]
      done;
      []
    with End_of_file -> 
      Unix.closedir dh; !lst
  with Unix.Unix_error (_,"opendir",_) ->
    failwith ("all_modules_in_dir: directory "^dir^" not found")

(* Gives a part of command line (corresponding to dir) for [extract_crc] *)
let crc_cmd dir =
  " -I "^dir^(List.fold_right (fun x y -> " "^x^y) (all_modules_in_dir dir)
  "")

(* Same as [crc_cmd] but recursively *)
let rec_crc_cmd dir =
  List.fold_right (fun x y -> x^y) (List.map crc_cmd (all_subdirs dir)) ""

(* Creates another temporary file for Dynlink if needed *)
let tmp_dynlink()=
  let tmp = Filename.temp_file "coqdynlink" ".ml" in
  let _ = Sys.command ("echo \"Dynlink.init();;\" > "^tmp) in
  let _ = Sys.command (Coq_config.camllib^"/extract_crc"^(crc_cmd
      Coq_config.camllib)^(crc_cmd Coq_config.camlp4lib)^(rec_crc_cmd
      Coq_config.coqtop)^" >> "^tmp) in
  let _ = Sys.command ("echo \";;\" >> "^tmp) in
  let _ = 
    Sys.command ("echo \"Dynlink.add_available_units crc_unit_list;;\" >> "^
		 tmp)
  in
  tmp

(* Initializes the kind of loading in the main program *)
let declare_loading_string () =
  if !opt then
    "Mltop.set Mltop.Native;;\n"
  else if not !top then
    "Mltop.set Mltop.WithoutTop;;\n"
  else
    "let ppf = Format.std_formatter;;
     Mltop.set (Mltop.WithTop
       {Mltop.load_obj=Topdirs.dir_load ppf;
        Mltop.use_file=Topdirs.dir_use ppf;
        Mltop.add_dir=Topdirs.dir_directory;
        Mltop.ml_loop=(fun () -> Toploop.loop ppf) });;\n"

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
    (* Start the right toplevel loop: Coq or Coq_searchisos *)
    if !searchisos then 
      output_string oc "Cmd_searchisos_line.start();;\n"
    else if !coqide then
      output_string oc "Coqide.start();;\n"
    else
      output_string oc "Coqtop.start();;\n";
    close_out oc;
    main_name
  with e -> 
    clean main_name; raise e

(* main part *)
let main () =
  let (options, userfiles) = parse_args () in
  (* which ocaml command to invoke *)
  let prog =
    if !opt then begin
      (* native code *)
      if !top then failwith "no custom toplevel in native code !";
      "ocamlopt -linkall"
    end else
      (* bytecode (we shunt ocamlmktop script which fails on win32) *)
      let ocamlmktoplib = " toplevellib.cma" in
      let ocamlccustom = "ocamlc -custom -linkall" in
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
    let args = options @ (includes ()) @ tolink @ dynlink @ [ main_file ] in
    (* add topstart.cmo explicitly because we shunted ocamlmktop wrapper *)
    let args = if !top then args @ [ "topstart.cmo" ] else args in
    (* Now, with the .cma, we MUST use the -linkall option *)
    let command = String.concat " " ((prog^" -linkall")::args) in
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
