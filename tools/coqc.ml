(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

(* Environment *)

let environment = Unix.environment ()

let binary = ref "coqtop"
let image = ref ""

let verbose = ref false

let rec make_compilation_args = function
  | [] -> []
  | file :: fl ->
      let file_noext =
        if Filename.check_suffix file ".v" then
          Filename.chop_suffix file ".v"
        else file
      in
      (if !verbose then "-compile-verbose" else "-compile")
      :: file_noext :: (make_compilation_args fl)

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

let usage () =
  Usage.print_usage_coqc () ;
  flush stderr ;
  exit 1

(* parsing of the command line *)
let extra_arg_needed = ref true

let parse_args () =
  let rec parse (cfiles,args) = function
    | [] ->
	List.rev cfiles, List.rev args
    | ("-verbose" | "--verbose") :: rem ->
	verbose := true ; parse (cfiles,args) rem
    | "-image" :: f :: rem -> image := f; parse (cfiles,args) rem
    | "-image" :: [] ->	usage ()
    | "-byte" :: rem -> binary := "coqtop.byte"; parse (cfiles,args) rem
    | "-opt" :: rem -> binary := "coqtop"; parse (cfiles,args) rem

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
      |"-impredicative-set"|"-vm"|"-no-native-compiler"
      |"-verbose-compat-notations"|"-no-compat-notations"
      |"-indices-matter"|"-quick"|"-color"
      |"-async-proofs-always-delegate"|"-async-proofs-never-reopen-branch"
      as o) :: rem ->
	parse (cfiles,o::args) rem

(* Options for coqtop : b) options with 1 argument *)

    | ("-outputstate"|"-inputstate"|"-is"|"-exclude-dir"
      |"-load-vernac-source"|"-l"|"-load-vernac-object"
      |"-load-ml-source"|"-require"|"-load-ml-object"
      |"-init-file"|"-dump-glob"|"-compat"|"-coqlib"
      |"-async-proofs-j" |"-async-proofs-private-flags" |"-async-proofs"
      as o) :: rem ->
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
    | "-Q" :: s :: t :: rem -> parse (cfiles,t::s::"-Q"::args) rem
    | ("-schedule-vio-checking"
      |"-check-vio-tasks" | "-schedule-vio2vo" as o) :: s :: rem ->
        let nodash, rem =
          CList.split_when (fun x -> String.length x > 1 && x.[0] = '-') rem in
        extra_arg_needed := false;
        parse (cfiles, List.rev nodash @ s :: o :: args) rem

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
    if cfiles = [] && !extra_arg_needed then begin
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
