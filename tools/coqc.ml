(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Coq compiler : coqc *)

(** For improving portability, coqc is now an OCaml program instead
    of a shell script. We use as much as possible the Sys and Filename
    module for better portability, but the Unix module is still used
    here and there (with explicitly qualified function names Unix.foo).

    We process here the commmand line to extract names of files to compile,
    then we compile them one by one while passing by the rest of the command
    line to a process running "coqtop -batch -compile <file>".
*)

let binary = ref "coqtop"
let image = ref ""

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
      let file_noext =
        if Filename.check_suffix file ".v" then
          Filename.chop_suffix file ".v"
        else file
      in
      check_module_name (Filename.basename file_noext);
      (if !verbose then "-compile-verbose" else "-compile")
      :: file_noext :: (make_compilation_args fl)

(* compilation of files [files] with command [command] and args [args] *)

let compile command args files =
  let args' = command :: args @ (make_compilation_args files) in
  Unix.execvp command (Array.of_list args')

let usage () =
  Usage.print_usage_coqc () ;
  flush stderr ;
  exit 1

(* parsing of the command line *)

let parse_args () =
  let rec parse (cfiles,args) = function
    | [] ->
	List.rev cfiles, List.rev args
    | ("-verbose" | "--verbose") :: rem ->
	verbose := true ; parse (cfiles,args) rem
    | "-image" :: f :: rem -> image := f; parse (cfiles,args) rem
    | "-image" :: [] ->	usage ()
    | "-byte" :: rem -> binary := "coqtop.byte"; parse (cfiles,args) rem
    | "-opt" :: rem -> (* now a no-op *) parse (cfiles,args) rem

(* Obsolete options *)

    | "-libdir" :: _ :: rem ->
        print_string "Warning: option -libdir deprecated and ignored\n";
        flush stdout;
        parse (cfiles,args) rem
    | ("-db"|"-debugger") :: rem ->
        print_string "Warning: option -db/-debugger deprecated and ignored\n";
        flush stdout;
        parse (cfiles,args) rem

(* Informative options *)

    | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> usage ()

    | ("-v"|"--version") :: _ -> Usage.version 0

    | ("-where") :: _ ->
        Envars.set_coqlib (fun x -> x);
        print_endline (Envars.coqlib ());
        exit 0

    | ("-config" | "--config") :: _ ->
        Envars.set_coqlib (fun x -> x);
        Usage.print_config ();
        exit 0

(* Options for coqtop : a) options with 0 argument *)

    | ("-notactics"|"-bt"|"-debug"|"-nolib"|"-boot"|"-time"
      |"-batch"|"-noinit"|"-nois"|"-noglob"|"-no-glob"
      |"-q"|"-full"|"-profile"|"-just-parsing"|"-echo" |"-unsafe"|"-quiet"
      |"-silent"|"-m"|"-xml"|"-v7"|"-v8"|"-beautify"|"-strict-implicit"
      |"-dont-load-proofs"|"-load-proofs"|"-force-load-proofs"
      |"-impredicative-set"|"-vm"|"-no-native-compiler"|"-quick"
      |"-verbose-compat-notations"|"-no-compat-notations" as o) :: rem ->
	parse (cfiles,o::args) rem

(* Options for coqtop : b) options with 1 argument *)

    | ("-outputstate"|"-inputstate"|"-is"|"-exclude-dir"
      |"-load-vernac-source"|"-l"|"-load-vernac-object"
      |"-load-ml-source"|"-require"|"-load-ml-object"
      |"-init-file"|"-dump-glob"|"-compat"|"-coqlib" as o) :: rem ->
	begin
	  match rem with
	    | s :: rem' -> parse (cfiles,s::o::args) rem'
	    | []        -> usage ()
	end

(* Options for coqtop : c) options with 1 argument and possibly more *)

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

(* Anything else is interpreted as a file *)

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
