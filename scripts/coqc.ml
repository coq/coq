(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* Afin de rendre Coq plus portable, ce programme Caml remplace le script
   coqc. 

   Ici, on trie la ligne de commande pour en extraire les fichiers � compiler,
   puis on les compile un par un en passant le reste de la ligne de commande
   � un process "coqtop -batch -load-vernac-source <fichier>".

   On essaye au maximum d'utiliser les modules Sys et Filename pour que la
   portabilit� soit maximale, mais il reste encore des appels � des fonctions
   du module Unix. Ceux-ci sont pr�fix�s par "Unix."
*)

(* environment *)

let environment = Unix.environment ()

let bindir = ref Coq_config.bindir
let binary = ref ("coqtop." ^ Coq_config.best)
let image = ref ""

(* the $COQBIN environment variable has priority over the Coq_config value *)
let _ = 
  try 
    let c = Sys.getenv "COQBIN" in
    if c <> "" then bindir := c
  with Not_found -> ()

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
  Unix.handle_unix_error
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
	bindir:= Filename.concat Coq_config.coqtop "bin";
	parse (cfiles, "-boot"::args) rem
    | "-bindir" :: d :: rem ->
	bindir := d ; parse (cfiles,args) rem
    | "-bindir" :: []       ->
	usage ()
    | "-byte" :: rem ->
	binary := "coqtop.byte"; parse (cfiles,args) rem
    | "-opt" :: rem ->
	binary := "coqtop.opt"; parse (cfiles,args) rem
    | "-image" :: f :: rem ->
	image := f; parse (cfiles,args) rem
    | "-image" :: [] ->
	usage ()
    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()
    | ("-libdir"|"-I"|"-include"|"-outputstate"
      |"-inputstate"|"-is"|"-load-vernac-source"|"-load-vernac-object"
      |"-load-ml-source"|"-require"|"-load-ml-object"|"-user"
      |"-init-file"|"-dump-glob" as o) :: rem ->
	begin
	  match rem with
	    | s :: rem' -> parse (cfiles,s::o::args) rem'
	    | []        -> usage ()
	end
    | "-R" as o :: s :: t :: rem -> parse (cfiles,t::s::o::args) rem
    | ("-notactics"|"-debug"|"-db"|"-debugger"|"-nolib"|"-batch"|"-nois"
      |"-q"|"-full"|"-profile"|"-just-parsing"|"-echo" |"-unsafe"|"-quiet"
      |"-silent"|"-m"|"-xml" as o) :: rem ->
	parse (cfiles,o::args) rem
    | ("-v"|"--version") :: _ ->
        Usage.version ()
    | "-where" :: _ -> 
	print_endline Coq_config.coqlib; exit 0
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
    if !image <> "" then !image else Filename.concat !bindir (!binary ^ Coq_config.exec_extension)
  in
(*  List.iter (compile coqtopname args) cfiles*)
  compile coqtopname args cfiles
    
let _ = Printexc.print main (); exit 0
