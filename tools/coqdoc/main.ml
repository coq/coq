(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Modified by Lionel Elie Mamane <lionel@mamane.lu> on 9 & 10 Mar 2004:
 *  - handling of absolute filenames (function coq_module)
 *  - coq_module: chop ./// (arbitrary amount of slashes), not only "./"
 *  - function chop_prefix not useful anymore. Deleted.
 *  - correct typo in usage message: "-R" -> "--R"
 *  - shorten the definition of make_path
 * This notice is made to comply with section 2.a of the GPLv2.
 * It may be removed or abbreviated as far as I am concerned.
 *)

open Cdglobals
open Filename
open Printf
open Output
open Pretty

(*s \textbf{Usage.} Printed on error output. *)

let usage () =
  prerr_endline "";
  prerr_endline "Usage: coqdoc <options and files>";
  prerr_endline "  --html              produce a HTML document (default)";
  prerr_endline "  --latex             produce a LaTeX document";
  prerr_endline "  --texmacs           produce a TeXmacs document";
  prerr_endline "  --dvi               output the DVI";
  prerr_endline "  --ps                output the PostScript";
  prerr_endline "  --stdout            write output to stdout";
  prerr_endline "  -o <file>           write output in file <file>";
  prerr_endline "  -d <dir>            output files into directory <dir>";
  prerr_endline "  -g                  (gallina) skip proofs";
  prerr_endline "  -s                  (short) no titles for files";
  prerr_endline "  -l                  light mode (only defs and statements)";
  prerr_endline "  -t <string>         give a title to the document";
  prerr_endline "  --body-only         suppress LaTeX/HTML header and trailer";
  prerr_endline "  --no-index          do not output the index";
  prerr_endline "  --multi-index       index split in multiple files";
  prerr_endline "  --toc               output a table of contents";
  prerr_endline "  --vernac <file>     consider <file> as a .v file";
  prerr_endline "  --tex <file>        consider <file> as a .tex file";
  prerr_endline "  -p <string>         insert <string> in LaTeX preamble";
  prerr_endline "  --files-from <file> read file names to process in <file>";
  prerr_endline "  --quiet             quiet mode";
  prerr_endline "  --glob-from <file>  read Coq globalizations from file <file>";
  prerr_endline "  --no-externals      no links to Coq standard library";
  prerr_endline "  --coqlib <url>      set URL for Coq standard library";
  prerr_endline "                      (default is http://coq.inria.fr/library/)";
  prerr_endline "  --coqlib_path <dir> set the path where Coq files are installed";
  prerr_endline "  -R <dir> <coqdir>   map physical dir to Coq dir";
  prerr_endline "  --latin1            set ISO-8859-1 input language";
  prerr_endline "  --utf8              set UTF-8 input language";
  prerr_endline "  --charset <string>  set HTML charset";
  prerr_endline "  --inputenc <string> set LaTeX input encoding";
  prerr_endline "";
  exit 1

(*s \textbf{Banner.} Always printed. Notice that it is printed on error
    output, so that when the output of [coqdoc] is redirected this header
    is not (unless both standard and error outputs are redirected, of 
    course). *)

let banner () =
  eprintf "This is coqdoc version %s, compiled on %s\n"
    Coq_config.version Coq_config.compile_date;
  flush stderr
    
let target_full_name f = 
  match !target_language with
    | HTML -> f ^ ".html"
    | _ -> f ^ ".tex"
	
(*s \textbf{Separation of files.} Files given on the command line are
    separated according to their type, which is determined by their
    suffix.  Coq files have suffixe \verb!.v! or \verb!.g! and \LaTeX\
    files have suffix \verb!.tex!. *)

let check_if_file_exists f =
  if not (Sys.file_exists f) then begin
    eprintf "\ncoqdoc: %s: no such file\n" f;
    exit 1
  end
    
let paths = ref []
  
let add_path m l = paths := (m,l) :: !paths
  
let exists_dir dir =
  try let _ = Unix.opendir dir in true with Unix.Unix_error _ -> false

let add_rec_path f l =
  let rec traverse abs rel =
    add_path abs rel;
    let dirh = Unix.opendir abs in
      try
	while true do
	  let f = Unix.readdir dirh in
	    if f <> "" && f.[0] <> '.' && f <> "CVS" then
	      let abs' = Filename.concat abs f in
		try 
		  if exists_dir abs' then  traverse abs' (rel ^ "." ^ f)
		with Unix.Unix_error _ -> 
		  ()
	done
      with End_of_file ->
	Unix.closedir dirh
  in
    if exists_dir f then traverse f l

(* turn A/B/C into A.B.C *)
let make_path = Str.global_replace (Str.regexp "/") ".";;

let coq_module file = 
  (* TODO
   * LEM:
   * We should also remove things like "/./" in the middle of the filename,
   * rewrite "/foo/../bar" to "/bar", recognise different paths that lead
   * to the same file / directory (via symlinks), etc. The best way to do
   * all this would be to use the libc function realpath() on _both_ p and
   * file / f before comparing them.
   *
   * The semantics of realpath() on file symlinks might not be what we
   * want... (But it is what we want on directory symlinks.) So, we would
   * have to cook up our own version of realpath()?
   *
   * Do all target platforms have realpath()?
   *)
  let f = chop_extension file in
    (* remove leading ./ and any number of slashes after *)
  let f = Str.replace_first (Str.regexp "^\\./+") "" f in
    if (Str.string_before f 1) = "/" then
      (* f is an absolute path. Prefixes must be matched with the beginning of f,
       * not prepended
       *)
      let rec trypath = function
	| [] -> make_path f
	| (p, lg) :: r ->
            (* make sure p ends with a single '/'
             * This guarantees that we don't match a file whose name is
             * of the form p ^ "foo". It means we may miss p itself,
             * but this does not matter: coqdoc doesn't do anything
             * of a directory anyway. *)
            let p = (Str.replace_first (Str.regexp "/*$") "/" p) in
            let p_quoted = (Str.quote p) in
              if (Str.string_match (Str.regexp p_quoted) f 0) then
		make_path (Filename.concat lg (Str.replace_first (Str.regexp (p_quoted ^ "/*")) "" f))
              else
		trypath r
      in trypath !paths
    else (* f is a relative path *)
      let rec trypath = function
	| [] -> 
	    make_path f
	| (p,lg) :: r ->
	    let p_file = Filename.concat p file in
	      if Sys.file_exists p_file then
		make_path (Filename.concat lg f)
	      else
		trypath r
      in trypath !paths;;

let what_file f =
  check_if_file_exists f;
  if check_suffix f ".v" || check_suffix f ".g" then
    Vernac_file (f, coq_module f)
  else if check_suffix f ".tex" then
    Latex_file f
  else begin
    eprintf "\ncoqdoc: don't know what to do with %s\n" f;
    exit 1
  end
    
(*s \textbf{Reading file names from a file.} 
 *  File names may be given
 *  in a file instead of being given on the command
 *  line. [(files_from_file f)] returns the list of file names contained
 *  in the file named [f]. These file names must be separated by spaces,
 *  tabulations or newlines.
 *)

let files_from_file f =
  let files_from_channel ch =
    let buf = Buffer.create 80 in
    let l = ref [] in
      try
	while true do
	  match input_char ch with
	    | ' ' | '\t' | '\n' ->
		if Buffer.length buf > 0 then l := (Buffer.contents buf) :: !l;
		Buffer.clear buf
	    | c -> 
		Buffer.add_char buf c
	done; []
      with End_of_file ->
	List.rev !l
  in
    try
      check_if_file_exists f;
      let ch = open_in f in
      let l = files_from_channel ch in
	close_in ch;l
    with Sys_error s -> begin
      eprintf "\ncoqdoc: cannot read from file %s (%s)\n" f s;
      exit 1
    end
      
(*s \textbf{Parsing of the command line.} *)
      
let output_file = ref ""
let dvi = ref false
let ps = ref false

let parse () =
  let files = ref [] in
  let add_file f = files := f :: !files in
  let rec parse_rec = function
    | [] -> ()
	
    | ("-nopreamble" | "--nopreamble" | "--no-preamble"
      |  "-bodyonly"   | "--bodyonly"   | "--body-only") :: rem ->
	header_trailer := false; parse_rec rem
    | ("-p" | "--preamble") :: s :: rem ->
	push_in_preamble s; parse_rec rem
    | ("-p" | "--preamble") :: [] ->
	usage ()
    | ("-noindex" | "--noindex" | "--no-index") :: rem ->
	index := false; parse_rec rem
    | ("-multi-index" | "--multi-index") :: rem ->
	multi_index := true; parse_rec rem
    | ("-toc" | "--toc" | "--table-of-contents") :: rem ->
	toc := true; parse_rec rem
    | ("-stdout" | "--stdout") :: rem ->
	out_to := StdOut; parse_rec rem
    | ("-o" | "--output") :: f :: rem ->
	out_to := File (Filename.basename f); output_dir := Filename.dirname f; parse_rec rem
    | ("-o" | "--output") :: [] -> 
	usage ()
    | ("-d" | "--directory") :: dir :: rem ->
	output_dir := dir; parse_rec rem
    | ("-d" | "--directory") :: [] -> 
	usage ()
    | ("-s" | "--short") :: rem ->
	short := true; parse_rec rem
    | ("-l" | "-light" | "--light") :: rem ->
	gallina := true; light := true; parse_rec rem
    | ("-g" | "-gallina" | "--gallina") :: rem ->
	gallina := true; parse_rec rem
    | ("-t" | "-title" | "--title") :: s :: rem ->
	title := s; parse_rec rem
    | ("-t" | "-title" | "--title") :: [] ->
	usage ()
    | ("-latex" | "--latex") :: rem ->
	Cdglobals.target_language := LaTeX; parse_rec rem
    | ("-dvi" | "--dvi") :: rem ->
	Cdglobals.target_language := LaTeX; dvi := true; parse_rec rem
    | ("-ps" | "--ps") :: rem ->
	Cdglobals.target_language := LaTeX; ps := true; parse_rec rem
    | ("-html" | "--html") :: rem ->
	Cdglobals.target_language := HTML; parse_rec rem
    | ("-texmacs" | "--texmacs") :: rem ->
	Cdglobals.target_language := TeXmacs; parse_rec rem
    | ("-charset" | "--charset") :: s :: rem ->
	Cdglobals.charset := s; parse_rec rem
    | ("-charset" | "--charset") :: [] ->
	usage ()
    | ("-inputenc" | "--inputenc") :: s :: rem ->
	Cdglobals.inputenc := s; parse_rec rem
    | ("-inputenc" | "--inputenc") :: [] ->
	usage ()
    | ("-raw-comments" | "--raw-comments") :: rem ->
	Cdglobals.raw_comments := true; parse_rec rem
    | ("-latin1" | "--latin1") :: rem ->
	Cdglobals.set_latin1 (); parse_rec rem
    | ("-utf8" | "--utf8") :: rem ->
	Cdglobals.set_utf8 (); parse_rec rem
	  
    | ("-q" | "-quiet" | "--quiet") :: rem ->
	quiet := true; parse_rec rem
	  
    | ("-h" | "-help" | "-?" | "--help") :: rem ->
	banner (); usage ()
    | ("-v" | "-version" | "--version") :: _ ->
	banner (); exit 0

    | ("-vernac-file" | "--vernac-file") :: f :: rem -> 
	check_if_file_exists f;
	add_file (Vernac_file (f, coq_module f)); parse_rec rem
    | ("-vernac-file" | "--vernac-file") :: [] ->
	usage ()
    | ("-tex-file" | "--tex-file") :: f :: rem -> 
	add_file (Latex_file f); parse_rec rem
    | ("-tex-file" | "--tex-file") :: [] ->
	usage ()
    | ("-files" | "--files" | "--files-from") :: f :: rem ->
	List.iter (fun f -> add_file (what_file f)) (files_from_file f); 
	parse_rec rem
    | ("-files" | "--files") :: [] ->
	usage ()
    | "-R" :: path :: log :: rem -> 
	add_path path log; parse_rec rem
    | "-R" :: ([] | [_]) ->
	usage ()
    | ("-glob-from" | "--glob-from") :: f :: rem ->
	Index.read_glob f; parse_rec rem
    | ("-glob-from" | "--glob-from") :: [] ->
	usage ()
    | ("--no-externals" | "-no-externals" | "-noexternals") :: rem ->
	Cdglobals.externals := false; parse_rec rem
    | ("--coqlib" | "-coqlib") :: u :: rem ->
	Cdglobals.coqlib := u; parse_rec rem
    | ("--coqlib" | "-coqlib") :: [] ->
	usage ()
    | ("--coqlib_path" | "-coqlib_path") :: d :: rem ->
	Cdglobals.coqlib_path := d; parse_rec rem
    | ("--coqlib_path" | "-coqlib_path") :: [] ->
	usage ()
    | f :: rem -> 
	add_file (what_file f); parse_rec rem
  in 
    parse_rec (List.tl (Array.to_list Sys.argv));
    List.rev !files

      
(*s The following function produces the output. The default output is
    the \LaTeX\ document: in that case, we just call [Web.produce_document]. 
    If option \verb!-dvi!, \verb!-ps! or \verb!-html! is invoked, then
    we make calls to \verb!latex! or \verb!dvips!  accordingly. *)

let locally dir f x =
  let cwd = Sys.getcwd () in
    try
      Sys.chdir dir; let y = f x in Sys.chdir cwd; y
    with e ->
      Sys.chdir cwd; raise e

let clean_temp_files basefile =
  let remove f = try Sys.remove f with _ -> () in
    remove (basefile ^ ".tex");
    remove (basefile ^ ".log");
    remove (basefile ^ ".aux");
    remove (basefile ^ ".dvi");
    remove (basefile ^ ".ps");
    remove (basefile ^ ".haux");
    remove (basefile ^ ".html")
      
let clean_and_exit file res = clean_temp_files file; exit res
  
let cat file =
  let c = open_in file in
    try
      while true do print_char (input_char c) done
    with End_of_file ->
      close_in c

let copy src dst =
  let cin = open_in src 
  and cout = open_out dst in
    try
      while true do Pervasives.output_char cout (input_char cin) done
    with End_of_file ->
      close_in cin; close_out cout


(*s Functions for generating output files *)
	
let gen_one_file l =
  let file = function
    | Vernac_file (f,m) -> 
	set_module m; coq_file f m
    | Latex_file _ -> ()
  in
    if (!header_trailer) then header ();
    if !toc then make_toc ();
    List.iter file l;
    if !index then make_index();
    if (!header_trailer) then trailer ()
      
let gen_mult_files l =
  let file = function
    | Vernac_file (f,m) -> 
	set_module m;
	let hf = target_full_name m in
	  open_out_file hf;
	  if (!header_trailer) then header (); 
	  if !toc then make_toc ();
	  coq_file f m; 
	  if (!header_trailer) then trailer ();
	  close_out_file()
    | Latex_file _ -> ()
  in
    List.iter file l;
    if (!index && !target_language=HTML) then begin
      if (!multi_index) then make_multi_index (); 
      open_out_file "index.html"; 
      page_title := (if !title <> "" then !title else "Index");
      if (!header_trailer) then header (); 
      make_index (); 
      if (!header_trailer) then trailer ();
      close_out_file()
    end;
    if (!toc && !target_language=HTML) then begin
      open_out_file "toc.html"; 
      page_title := (if !title <> "" then !title else "Table of contents");
      if (!header_trailer) then header ();
      if !title <> "" then printf "<h1>%s</h1>\n" !title;
      make_toc (); 
      if (!header_trailer) then trailer ();
      close_out_file()
    end 
      (* Rq: pour latex et texmacs, une toc ou un index s�par� n'a pas de sens... *)


let index_module = function
  | Vernac_file (_,m) -> Index.add_module m
  | Latex_file _ -> ()
      
let produce_document l =
  List.iter index_module l;
  (if !target_language=HTML then
    let src = (Filename.concat !Cdglobals.coqlib_path "/tools/coqdoc/coqdoc.css") in
    let dst = if !output_dir <> "" then Filename.concat !output_dir "coqdoc.css" else "coqdoc.css" in
      copy src dst);
  (if !target_language=LaTeX then
    let src = (Filename.concat !Cdglobals.coqlib_path "/tools/coqdoc/coqdoc.sty") in
    let dst = if !output_dir <> "" then 
      Filename.concat !output_dir "coqdoc.sty" 
    else "coqdoc.sty" in
      copy src dst);
  match !out_to with
    | StdOut -> 
	Cdglobals.out_channel := stdout;
	gen_one_file l
    | File f ->
	open_out_file f;
	gen_one_file l;
	close_out_file()
    | MultFiles ->
	gen_mult_files l
	  
let produce_output fl =
  if not (!dvi || !ps) then begin
    produce_document fl
  end else begin
    let texfile = temp_file "coqdoc" ".tex" in
    let basefile = chop_suffix texfile ".tex" in
      open_out_file texfile;
      produce_document fl;
      let command = 
	let file = basename texfile in
	let file = 
	  if !quiet then sprintf "'\\nonstopmode\\input{%s}'" file else file 
	in
	  sprintf "(latex %s && latex %s) 1>&2 %s" file file
	    (if !quiet then "> /dev/null" else "")
      in
      let res = locally (dirname texfile) Sys.command command in
	if res <> 0 then begin
	  eprintf "Couldn't run LaTeX successfully\n"; 
	  clean_and_exit basefile res
	end;
	let dvifile = basefile ^ ".dvi" in
	  if !dvi then begin
	    if !output_file <> "" then 
	      (* we cannot use Sys.rename accross file systems *)
	      copy dvifile !output_file 
	    else 
	      cat dvifile
	  end;
	  if !ps then begin
	    let psfile = 
	      if !output_file <> "" then !output_file else basefile ^ ".ps" 
	    in
	    let command = 
	      sprintf "dvips %s -o %s %s" dvifile psfile 
		(if !quiet then "> /dev/null 2>&1" else "")
	    in
	    let res = Sys.command command in
	      if res <> 0 then begin
		eprintf "Couldn't run dvips successfully\n"; 
		clean_and_exit basefile res
	      end;
	      if !output_file = "" then cat psfile
	  end;
	  clean_temp_files basefile
  end


(*s \textbf{Main program.} Print the banner, parse the command line,
    read the files and then call [produce_document] from module [Web]. *)

let main () =
  let files = parse () in
    if not !quiet then banner ();
    if files <> [] then produce_output files
      
let _ = Printexc.catch main ()
