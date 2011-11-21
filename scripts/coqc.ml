(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Afin de rendre Coq plus portable, ce programme Caml remplace le script
   coqc.

   Ici, on trie la ligne de commande pour en extraire les fichiers à compiler,
   puis on les compile un par un en passant le reste de la ligne de commande
   à un process "coqtop -batch -load-vernac-source <fichier>".

   On essaye au maximum d'utiliser les modules Sys et Filename pour que la
   portabilité soit maximale, mais il reste encore des appels à des fonctions
   du module Unix. Ceux-ci sont préfixés par "Unix."
*)

(* environment *)

let environment = Unix.environment ()

let best = if Coq_config.arch = "win32" then "" else ("."^Coq_config.best)
let binary = ref ("coqtop" ^ best)
let image = ref ""

(* coqc options *)

let specification = ref false
let keep = ref false
let verbose = ref false

(* Verifies that a string starts by a letter and do not contain
   others caracters than letters, digits, or `_` *)

let check_module_name s =
  let err c =
    output_string stderr "Invalid module name: ";
    output_string stderr s;
    output_string stderr " character ";
    if c = '\'' then
      output_string stderr "\"'\""
    else
      (output_string stderr"'"; output_char stderr c; output_string stderr"'");
    output_string stderr " is not allowed in module names\n";
    exit 1
  in
  match String.get s 0 with
    | 'a' .. 'z' | 'A' .. 'Z' ->
	for i = 1 to (String.length s)-1 do
	  match String.get s i with
	    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_'  -> ()
	    | c -> err c
	done
    | c -> err c

let rec make_compilation_args = function
  | [] -> []
  | file :: fl ->
      let dirname = Filename.dirname file in
      let basename = Filename.basename file in
      let modulename =
        if Filename.check_suffix basename ".v" then
          Filename.chop_suffix basename ".v"
        else
          basename
      in
      check_module_name modulename;
      let file = Filename.concat dirname modulename in
      (if !verbose then "-compile-verbose" else "-compile")
      :: file :: (make_compilation_args fl)

(* compilation of files [files] with command [command] and args [args] *)

let compile command args files =
  let args' = command :: args @ (make_compilation_args files) in
  match Sys.os_type with
  | "Win32" ->
     let pid =
        Unix.create_process_env command (Array.of_list args') environment
        Unix.stdin Unix.stdout Unix.stderr
     in
     let status = snd (Unix.waitpid [] pid) in
     let errcode =
       match status with Unix.WEXITED c|Unix.WSTOPPED c|Unix.WSIGNALED c -> c
     in
     exit errcode
  | _ ->
     Unix.execvpe command (Array.of_list args') environment

(* parsing of the command line
 *
 * special treatment for -bindir and -i.
 * other options are passed to coqtop *)

let usage () =
  Usage.print_usage_coqc () ;
  flush stderr ;
  exit 1

let parse_args () =
  let rec parse (cfiles,args) = function
    | [] ->
	List.rev cfiles, List.rev args
    | "-i" :: rem ->
	specification := true ; parse (cfiles,args) rem
    | "-t" :: rem ->
	keep := true ; parse (cfiles,args) rem
    | ("-verbose" | "--verbose") :: rem ->
	verbose := true ; parse (cfiles,args) rem
    | "-boot" :: rem ->
	Flags.boot := true;
	parse (cfiles, "-boot"::args) rem
    | "-byte" :: rem ->
	binary := "coqtop.byte"; parse (cfiles,args) rem
    | "-opt" :: rem ->
	binary := "coqtop.opt"; parse (cfiles,args) rem
    | "-image" :: f :: rem ->
	image := f; parse (cfiles,args) rem
    | "-image" :: [] ->
	usage ()
    | "-libdir" :: _ :: rem ->
        print_string "Warning: option -libdir deprecated\n"; flush stdout;
        parse (cfiles,args) rem
    | ("-db"|"-debugger") :: rem ->
        print_string "Warning: option -db/-debugger deprecated\n";flush stdout;
        parse (cfiles,args) rem

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()
    | ("-outputstate"|"-inputstate"|"-is"
      |"-load-vernac-source"|"-l"|"-load-vernac-object"
      |"-load-ml-source"|"-require"|"-load-ml-object"
      |"-init-file"|"-dump-glob"|"-compat"|"-coqlib" as o) :: rem ->
	begin
	  match rem with
	    | s :: rem' -> parse (cfiles,s::o::args) rem'
	    | []        -> usage ()
	end
    | ("-I"|"-include" as o) :: rem ->
	begin
	  match rem with
	  | s :: "-as" :: t :: rem' -> parse (cfiles,t::"-as"::s::o::args) rem'
	  | s :: "-as" :: [] -> usage ()
	  | s :: rem' -> parse (cfiles,s::o::args) rem'
	  | []        -> usage ()
	end
    | "-R" :: s :: "-as" :: t :: rem ->	parse (cfiles,t::"-as"::s::"-R"::args) rem
    | "-R" :: s :: "-as" :: [] -> usage ()
    | "-R" :: s :: t :: rem -> parse (cfiles,t::s::"-R"::args) rem

    | ("-notactics"|"-debug"|"-nolib"
      |"-batch"|"-nois"|"-noglob"|"-no-glob"
      |"-q"|"-full"|"-profile"|"-just-parsing"|"-echo" |"-unsafe"|"-quiet"
      |"-silent"|"-m"|"-xml"|"-v7"|"-v8"|"-beautify"|"-strict-implicit"
      |"-dont-load-proofs"|"-load-proofs"|"-force-load-proofs"
      |"-impredicative-set"|"-vm" as o) :: rem ->
	parse (cfiles,o::args) rem

    | ("-where") :: _ ->
	(try print_endline (Envars.coqlib ())
	 with Util.UserError(_,pps) -> Pp.msgerrnl (Pp.hov 0 pps));
	exit 0

    | ("-config" | "--config") :: _ -> Usage.print_config (); exit 0

    | ("-v"|"--version") :: _ ->
        Usage.version 0
    | f :: rem ->
	if Sys.file_exists f then
	  parse (f::cfiles,args) rem
	else
	  let fv = f ^ ".v" in
	  if Sys.file_exists fv then
	    parse (fv::cfiles,args) rem
	  else begin
	    prerr_endline ("coqc: "^f^": no such file or directory") ;
	    exit 1
	  end
  in
  parse ([],[]) (List.tl (Array.to_list Sys.argv))

(* main: we parse the command line, define the command to compile files
 * and then call the compilation on each file *)

let main () =
  let cfiles, args = parse_args () in
    if cfiles = [] then begin
      prerr_endline "coqc: too few arguments" ;
      usage ()
    end;
    let coqtopname =
      if !image <> "" then !image
      else Filename.concat Envars.coqbin (!binary ^ Coq_config.exec_extension)
    in
      (*  List.iter (compile coqtopname args) cfiles*)
      Unix.handle_unix_error (compile coqtopname args) cfiles

let _ = Printexc.print main ()
