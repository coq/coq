
(* $Id$ *)

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

let bindir = ref Coq_config.bindir
let binary = ref "coqtop.byte"

(* the $COQBIN environment variable has priority over the Coq_config value *)
let _ = 
  try 
    let c = Sys.getenv "COQBIN" in
    if c <> "" then bindir := c
  with Not_found -> ()

let specification = ref false

let keep = ref false

(* Verifies that a string do not contains others caracters than letters, 
   digits, or `_` *)

let check_module_name s = 
  let err () = 
    output_string stderr
      "Modules names must only contain letters, digits, or underscores\n"; 
    output_string stderr
      "and must begin with a letter\n";
    exit 1 
  in
  match String.get s 0 with 
    | 'a' .. 'z' | 'A' .. 'Z' -> 
	for i = 1 to (String.length s)-1 do
	  match String.get s i with 
	    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_'  -> ()
	    | _ -> err ()
	done
    | _ -> err ()

 (* compilation of a file [file] with command [command] and args [args] *)

let compile command args file =
  let dirname = Filename.dirname file in
  let basename = Filename.basename file in
  let modulename =
    if Filename.check_suffix basename ".v" then
      Filename.chop_suffix basename ".v"
    else
      basename 
  in
  check_module_name modulename;
  let tmpfile = Filename.temp_file "coqc" ".v" in
  let args' = 
    command :: "-batch" :: "-silent" :: args 
    @ ["-load-vernac-source"; tmpfile] in
  let devnull = 
    if Sys.os_type = "Unix" then
      Unix.openfile "/dev/null" [] 0o777 
    else 
      Unix.stdin
  in 
  let filevo = Filename.concat dirname (modulename ^ ".vo") in
  let oc = open_out tmpfile in
  Printf.fprintf oc "Module %s.\n" modulename;
  Printf.fprintf oc "Load \"%s\".\n" file;
  Printf.fprintf oc "Write Module %s \"%s\".\n" modulename filevo;
  flush oc;
  close_out oc;
  try
    let pid =
      Unix.create_process_env command
        (Array.of_list args') environment devnull Unix.stdout Unix.stderr in
    let status = Unix.waitpid [] pid in
    if not !keep then Sys.remove tmpfile ;
    match status with
      | _, Unix.WEXITED 0 -> ()
      | _, Unix.WEXITED 127 -> 
	  Printf.printf "Cannot execute %s\n" command;
	  exit 1
      | _, Unix.WEXITED c -> exit c
      | _                 -> exit 1
  with _ -> 
    if not !keep then Sys.remove tmpfile; exit 1

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
    | "-bindir" :: d :: rem ->
	bindir := d ; parse (cfiles,args) rem
    | "-bindir" :: []       ->
	usage ()
    | "-byte" :: rem ->
	binary := "coqtop.byte"; parse (cfiles,args) rem
    | "-opt" :: rem ->
	binary := "coqtop.opt"; parse (cfiles,args) rem
    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()
    | ("-image"|"-libdir"|"-I"|"-R"|"-include"|"-outputstate"|"-inputstate"
      |"-is"|"-load-vernac-source"|"-load-vernac-object"|"-load-ml-source"
      |"-require"|"-unsafe"|"-quiet"|"-silent"|"-v"|"--version"
      |"-load-ml-object"|"-user"|"-init-file" as o) :: rem ->
	begin
	  match rem with
	    | s :: rem' -> parse (cfiles,s::o::args) rem'
	    | []        -> usage ()
	end
    | ("-notactics"|"-debug"|"-db"|"-debugger"|"-nolib"|"-batch"|"-nois"
      |"-q"|"-full"|"-profile"|"-just-parsing"|"-echo" as o) :: rem ->
	parse (cfiles,o::args) rem
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
  let coqtopname = Filename.concat !bindir !binary in
  List.iter (compile coqtopname args) cfiles
    
let _ = Printexc.print main (); exit 0
