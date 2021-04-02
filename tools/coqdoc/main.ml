(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Cdglobals
open Printf

(*s \textbf{Usage.} Printed on error output. *)

let usage () =
  prerr_endline "";
  prerr_endline "Usage: coqdoc <options and files>";
  prerr_endline "  --html               produce a HTML document (default)";
  prerr_endline "  --latex              produce a LaTeX document";
  prerr_endline "  --texmacs            produce a TeXmacs document";
  prerr_endline "  --raw                produce a text document";
  prerr_endline "  --dvi                output the DVI";
  prerr_endline "  --ps                 output the PostScript";
  prerr_endline "  --pdf                output the Pdf";
  prerr_endline "  --stdout             write output to stdout";
  prerr_endline "  -o <file>            write output in file <file>";
  prerr_endline "  -d <dir>             output files into directory <dir>";
  prerr_endline "  -g                   (gallina) skip proofs";
  prerr_endline "  -s                   (short) no titles for files";
  prerr_endline "  -l                   light mode (only defs and statements)";
  prerr_endline "  -t <string>          give a title to the document";
  prerr_endline "  --body-only          suppress LaTeX/HTML header and trailer";
  prerr_endline "  --with-header <file> prepend <file> as html reader";
  prerr_endline "  --with-footer <file> append <file> as html footer";
  prerr_endline "  --no-index           do not output the index";
  prerr_endline "  --multi-index        index split in multiple files";
  prerr_endline "  --index <string>     set index name (default is index)";
  prerr_endline "  --toc                output a table of contents";
  prerr_endline "  --vernac <file>      consider <file> as a .v file";
  prerr_endline "  --tex <file>         consider <file> as a .tex file";
  prerr_endline "  -p <string>          insert <string> in LaTeX preamble";
  prerr_endline "  --files-from <file>  read file names to process in <file>";
  prerr_endline "  --glob-from <file>   read globalization information from <file>";
  prerr_endline "  --no-glob            don't use any globalization information (no links will be inserted at identifiers)";
  prerr_endline "  --quiet              quiet mode (default)";
  prerr_endline "  --verbose            verbose mode";
  prerr_endline "  --no-externals       no links to Coq standard library";
  prerr_endline "  --external <url> <d> set URL for external library d";
  prerr_endline "  --coqlib_url <url>   set URL for Coq standard library";
  prerr_endline ("                       (default is " ^ Coq_config.wwwstdlib ^ ")");
  prerr_endline "  --boot               run in boot mode (no-op)";
  prerr_endline "  --coqlib <dir>       set the path where Coq files are installed";
  prerr_endline "  -R <dir> <coqdir>    map physical dir to Coq dir";
  prerr_endline "  -Q <dir> <coqdir>    map physical dir to Coq dir";
  prerr_endline "  --latin1             set ISO-8859-1 mode";
  prerr_endline "  --utf8               set UTF-8 mode";
  prerr_endline "  --charset <string>   set HTML charset";
  prerr_endline "  --inputenc <string>  set LaTeX input encoding";
  prerr_endline "  --interpolate        try to typeset identifiers in comments using definitions in the same module";
  prerr_endline "  --parse-comments     parse regular comments";
  prerr_endline "  --plain-comments     consider comments as non-literate text";
  prerr_endline "  --toc-depth <int>    don't include TOC entries for sections below level <int>";
  prerr_endline "  --no-lib-name        don't display \"Library\" before library names in the toc";
  prerr_endline "  --lib-name <string>  call top level toc entries <string> instead of \"Library\"";
  prerr_endline "  --lib-subtitles      first line comments of the form (** * ModuleName : text *) will be interpreted as subtitles";
  prerr_endline "  --inline-notmono     use a proportional width font for inline code (possibly with a different color)";
  prerr_endline "";
  exit 1

(*s \textbf{Banner.} Always printed. Notice that it is printed on error
    output, so that when the output of [coqdoc] is redirected this header
    is not (unless both standard and error outputs are redirected, of
    course). *)

let banner () =
  eprintf "This is coqdoc version %s\n" Coq_config.version;
  flush stderr

let target_full_name f =
  match !Cdglobals.target_language with
    | HTML -> f ^ ".html"
    | Raw -> f ^ ".txt"
    | _ -> f ^ ".tex"

(*s \textbf{Separation of files.} Files given on the command line are
    separated according to their type, which is determined by their
    suffix.  Coq files have suffixe \verb!.v! or \verb!.g! and \LaTeX\
    files have suffix \verb!.tex!. *)

(* [paths] maps a physical path to a name *)
let paths = ref []

let add_path dir name =
  let p = normalize_path dir in
  paths := (p,name) :: !paths

(* turn A/B/C into A.B.C *)
let rec name_of_path p name dirname suffix =
  if p = dirname then String.concat "." (if name = "" then suffix else (name::suffix))
  else
    let subdir = Filename.dirname dirname in
    if subdir = dirname then raise Not_found
    else name_of_path p name subdir (Filename.basename dirname::suffix)

let coq_module filename =
  let bfname = Filename.chop_extension filename in
  let dirname, fname = normalize_filename bfname in
  let _ = match Unicode.ident_refutation fname with
    | Some err -> eprintf "\ncoqdoc: not a valid filename %s.v\n" fname; exit 1
    | None -> () in
  let rec change_prefix = function
    (* Follow coqc: if in scope of -R, substitute logical name *)
    (* otherwise, keep only base name *)
    | [] -> fname
    | (p, name) :: rem ->
        try name_of_path p name dirname [fname]
        with Not_found -> change_prefix rem
  in
  change_prefix !paths

let what_file f =
  FileUtil.check_if_file_exists f;
  if Filename.check_suffix f ".v" || Filename.check_suffix f ".g" then
    Vernac_file (f, coq_module f)
  else if Filename.check_suffix f ".tex" then
    Latex_file f
  else
     (eprintf "\ncoqdoc: don't know what to do with %s\n" f; exit 1)

(*s \textbf{Parsing of the command line.} *)

let compile_targets = ref []
type glob_source_t = NoGlob | DotGlob | GlobFile of string
let glob_source = ref DotGlob

let parse () =
  let files = ref [] in
  let add_file f = files := f :: !files in
  let rec parse_rec = function
    | [] -> ()

    | ("-nopreamble" | "--nopreamble" | "--no-preamble"
      |  "-bodyonly"   | "--bodyonly"   | "--body-only") :: rem ->
        header_trailer := false; parse_rec rem
    | ("-with-header" | "--with-header") :: f ::rem ->
        header_trailer := true; header_file_spec := true; header_file := f; parse_rec rem
    | ("-with-header" | "--with-header") :: [] ->
        usage ()
    | ("-with-footer" | "--with-footer") :: f ::rem ->
        header_trailer := true; footer_file_spec := true; footer_file := f; parse_rec rem
    | ("-with-footer" | "--with-footer") :: [] ->
        usage ()
    | ("-p" | "--preamble") :: s :: rem ->
        Output.push_in_preamble s; parse_rec rem
    | ("-p" | "--preamble") :: [] ->
        usage ()
    | ("-noindex" | "--noindex" | "--no-index") :: rem ->
        index := false; parse_rec rem
    | ("-multi-index" | "--multi-index") :: rem ->
        multi_index := true; parse_rec rem
    | ("-index" | "--index") :: s :: rem ->
        Cdglobals.index_name := s; parse_rec rem
    | ("-index" | "--index") :: [] ->
        usage ()
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
        Cdglobals.target_language := LaTeX;
        parse_rec rem
    | ("-pdf" | "--pdf") :: rem ->
        Cdglobals.target_language := LaTeX;
        compile_targets := LatexCompiler.Pdf :: !compile_targets;
        parse_rec rem
    | ("-dvi" | "--dvi") :: rem ->
        Cdglobals.target_language := LaTeX;
        compile_targets := LatexCompiler.Dvi :: !compile_targets;
        parse_rec rem
    | ("-ps" | "--ps") :: rem ->
        Cdglobals.target_language := LaTeX;
        compile_targets := LatexCompiler.Ps :: !compile_targets;
        parse_rec rem
    | ("-html" | "--html") :: rem ->
        Cdglobals.target_language := HTML; parse_rec rem
    | ("-texmacs" | "--texmacs") :: rem ->
        Cdglobals.target_language := TeXmacs; parse_rec rem
    | ("-raw" | "--raw") :: rem ->
        Cdglobals.target_language := Raw; parse_rec rem
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
    | ("-parse-comments" | "--parse-comments") :: rem ->
        Cdglobals.parse_comments := true; parse_rec rem
    | ("-plain-comments" | "--plain-comments") :: rem ->
        Cdglobals.plain_comments := true; parse_rec rem
    | ("-interpolate" | "--interpolate") :: rem ->
        Cdglobals.interpolate := true; parse_rec rem
    | ("-toc-depth" | "--toc-depth") :: [] ->
      usage ()
    | ("-toc-depth" | "--toc-depth") :: ds :: rem ->
      let d = try int_of_string ds with
                Failure _ ->
                  (eprintf "--toc-depth must be followed by an integer\n";
                   exit 1)
      in
      Cdglobals.toc_depth := Some d;
      parse_rec rem
    | ("-no-lib-name" | "--no-lib-name") :: rem ->
      Cdglobals.lib_name := "";
      parse_rec rem
    | ("-lib-name" | "--lib-name") :: ds :: rem ->
      Cdglobals.lib_name := ds;
      parse_rec rem
    | ("-lib-subtitles" | "--lib-subtitles") :: rem ->
      Cdglobals.lib_subtitles := true;
      parse_rec rem
    | ("-inline-notmono" | "--inline-notmono") :: rem ->
      Cdglobals.inline_notmono := true;
      parse_rec rem

    | ("-latin1" | "--latin1") :: rem ->
        Cdglobals.set_latin1 (); parse_rec rem
    | ("-utf8" | "--utf8") :: rem ->
        Cdglobals.set_utf8 (); parse_rec rem

    | ("-q" | "-quiet" | "--quiet") :: rem ->
        quiet := true; parse_rec rem
    | ("-v" | "-verbose" | "--verbose") :: rem ->
        quiet := false; parse_rec rem

    | ("-h" | "-help" | "-?" | "--help") :: rem ->
        banner (); usage ()
    | ("-V" | "-version" | "--version") :: _ ->
        banner (); exit 0

    | ("-vernac-file" | "--vernac-file") :: f :: rem ->
        FileUtil.check_if_file_exists f;
        add_file (Vernac_file (f, coq_module f)); parse_rec rem
    | ("-vernac-file" | "--vernac-file") :: [] ->
        usage ()
    | ("-tex-file" | "--tex-file") :: f :: rem ->
        add_file (Latex_file f); parse_rec rem
    | ("-tex-file" | "--tex-file") :: [] ->
        usage ()
    | ("-files" | "--files" | "--files-from") :: f :: rem ->
        List.iter (fun f -> add_file (what_file f)) (FileUtil.files_from_file f);
        parse_rec rem
    | ("-files" | "--files") :: [] ->
        usage ()
    | "-R" :: path :: log :: rem ->
        add_path path log; parse_rec rem
    | "-R" :: ([] | [_]) ->
        usage ()
    | "-Q" :: path :: log :: rem ->
        add_path path log; parse_rec rem
    | "-Q" :: ([] | [_]) ->
        usage ()
    | ("-glob-from" | "--glob-from") :: f :: rem ->
        glob_source := GlobFile f; parse_rec rem
    | ("-glob-from" | "--glob-from") :: [] ->
        usage ()
    | ("-no-glob" | "--no-glob") :: rem ->
        glob_source := NoGlob; parse_rec rem
    | ("--no-externals" | "-no-externals" | "-noexternals") :: rem ->
        Cdglobals.externals := false; parse_rec rem
    | ("--external" | "-external") :: u :: logicalpath :: rem ->
        Index.add_external_library logicalpath u; parse_rec rem
    | ("--coqlib_url" | "-coqlib_url") :: u :: rem ->
        Cdglobals.coqlib_url := u; parse_rec rem
    | ("--coqlib_url" | "-coqlib_url") :: [] ->
        usage ()
    | ("--boot" | "-boot") :: rem ->
        (* XXX: This is useless it seems *)
        parse_rec rem
    | ("--coqlib" | "-coqlib") :: d :: rem ->
        Boot.Env.set_coqlib d; parse_rec rem
    | ("--coqlib" | "-coqlib") :: [] ->
        usage ()
    | f :: rem ->
        add_file (what_file f); parse_rec rem
  in
    parse_rec (List.tl (Array.to_list Sys.argv));
    List.rev !files


(*s The following function produces the output. The default output is
    the \LaTeX\ document: in that case, we just call [Web.produce_document].
    If option \verb!-dvi!, \verb!-ps! or \verb!-html! is invoked, then
    we make calls to \verb!latex! or \verb!dvips! or \verb!pdflatex! accordingly. *)

(*s Functions for generating output files *)

let gen_one_file l =
  let file = function
    | Vernac_file (f,m) ->
      let sub = if !lib_subtitles then Cpretty.detect_subtitle f m else None in
      Output.set_module m sub;
      Cpretty.coq_file f m
    | Latex_file _ -> ()
  in
    if (!header_trailer) then Output.header ();
    if !toc then Output.make_toc ();
    List.iter file l;
    if !index then Output.make_index();
    if (!header_trailer) then Output.trailer ()

let gen_mult_files l =
  let file = function
    | Vernac_file (f,m) ->
      let sub = if !lib_subtitles then Cpretty.detect_subtitle f m else None in
        let hf = target_full_name m in
        Output.set_module m sub;
          open_out_file hf;
          if (!header_trailer) then Output.header ();
          Cpretty.coq_file f m;
          if (!header_trailer) then Output.trailer ();
          close_out_file()
    | Latex_file _ -> ()
  in
    List.iter file l;
    if (!index && !target_language=HTML) then begin
      if (!multi_index) then Output.make_multi_index ();
      open_out_file (!index_name^".html");
      page_title := (if !title <> "" then !title else "Index");
      if (!header_trailer) then Output.header ();
      Output.make_index ();
      if (!header_trailer) then Output.trailer ();
      close_out_file()
    end;
    if (!toc && !target_language=HTML) then begin
      open_out_file "toc.html";
      page_title := (if !title <> "" then !title else "Table of contents");
      if (!header_trailer) then Output.header ();
      if !title <> "" then printf "<h1>%s</h1>\n" !title;
      Output.make_toc ();
      if (!header_trailer) then Output.trailer ();
      close_out_file()
    end
    (* NB: for latex and texmacs, a separated toc or index is meaningless... *)

let read_glob_file vfile f =
  try Glob_file.read_glob vfile f
  with Sys_error s -> eprintf "Warning: %s (links will not be available)\n" s

let read_glob_file_of = function
  | Vernac_file (f,_) ->
    read_glob_file (Some f) (Filename.chop_extension f ^ ".glob")
  | Latex_file _ -> ()

let index_module = function
  | Vernac_file (f,m) ->
    Index.add_module m
  | Latex_file _ -> ()

module E = Boot.Env

let copy_style_file file =
  (* We give preference to coqlib in case it is overriden *)
  let env = E.init () in
  let coqdoc = E.tool env "coqdoc" in
  let sty_file = E.Path.relative coqdoc file in
  if not (E.Path.exists sty_file) then
    begin
      let sty_file = E.Path.to_string sty_file in
      eprintf "coqdoc: cannot find coqdoc style file: %s\n" sty_file;
      exit 1
    end;
  let sty_file_s = E.Path.to_string sty_file in
  let dst = coqdoc_out file in
  FileUtil.copy sty_file_s dst

let produce_document l =
  if !target_language=HTML then copy_style_file "coqdoc.css";
  if !target_language=LaTeX then copy_style_file "coqdoc.sty";
  (match !glob_source with
    | NoGlob -> ()
    | DotGlob -> List.iter read_glob_file_of l
    | GlobFile f -> read_glob_file None f);
  List.iter index_module l;
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
  if List.length !compile_targets = 0 then
    produce_document fl
  else
    let otypes = !compile_targets in
    LatexCompiler.compile ~otypes ~produce_document fl

(*s \textbf{Main program.} Print the banner, parse the command line,
    read the files and then call [produce_document] from module [Web]. *)

let _ =
  let files = parse () in
  Index.init_coqlib_library ();
    if not !quiet then banner ();
    if files <> [] then produce_output files
