(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf
open Common

(*s \textbf{Banner.} Always printed. Notice that it is printed on error
    output, so that when the output of [coqdoc] is redirected this header
    is not (unless both standard and error outputs are redirected, of
    course). *)

let banner () =
  eprintf "This is coqdoc version %s\n" Coq_config.version;
  flush stderr

let target_full_name f =
  match !prefs.targetlang with
    | HTML -> f ^ ".html"
    | Raw -> f ^ ".txt"
    | _ -> f ^ ".tex"

(*s The following function produces the output. The default output is
    the \LaTeX\ document: in that case, we just call [Web.produce_document].
    If option \verb!-dvi!, \verb!-ps! or \verb!-html! is invoked, then
    we make calls to \verb!latex! or \verb!dvips! or \verb!pdflatex! accordingly. *)

(*s Functions for generating output files *)

let gen_one_file l =
  let file = function
    | Vernac_file (f,m) ->
      let sub = if !prefs.lib_subtitles then Cpretty.detect_subtitle f m else None in
      Output.set_module m sub;
      Cpretty.coq_file f m
    | Latex_file _ -> ()
  in
    if (!prefs.header_trailer) then Output.header ();
    if !prefs.toc then Output.make_toc ();
    List.iter file l;
    if !prefs.index then Output.make_index();
    if (!prefs.header_trailer) then Output.trailer ()

let gen_mult_files l =
  let file = function
    | Vernac_file (f,m) ->
      let sub = if !prefs.lib_subtitles then Cpretty.detect_subtitle f m else None in
        let hf = target_full_name m in
        Output.set_module m sub;
          open_out_file hf;
          if (!prefs.header_trailer) then Output.header ();
          Cpretty.coq_file f m;
          if (!prefs.header_trailer) then Output.trailer ();
          close_out_file()
    | Latex_file _ -> ()
  in
    List.iter file l;
    if (!prefs.index && !prefs.targetlang=HTML) then begin
      if (!prefs.multi_index) then Output.make_multi_index ();
      open_out_file (!prefs.index_name^".html");
      page_title := (if !prefs.title <> "" then !prefs.title else "Index");
      if (!prefs.header_trailer) then Output.header ();
      Output.make_index ();
      if (!prefs.header_trailer) then Output.trailer ();
      close_out_file()
    end;
    if (!prefs.toc && !prefs.targetlang=HTML) then begin
      open_out_file "toc.html";
      page_title := (if !prefs.title <> "" then !prefs.title else "Table of contents");
      if (!prefs.header_trailer) then Output.header ();
      if !prefs.title <> "" then printf "<h1>%s</h1>\n" !prefs.title;
      Output.make_toc ();
      if (!prefs.header_trailer) then Output.trailer ();
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
  if !prefs.targetlang=HTML then copy_style_file "coqdoc.css";
  if !prefs.targetlang=LaTeX then copy_style_file "coqdoc.sty";
  (match !prefs.glob_source with
    | NoGlob -> ()
    | DotGlob -> List.iter read_glob_file_of l
    | GlobFile f -> read_glob_file None f);
  List.iter index_module l;
  match !prefs.out_to with
    | StdOut ->
        Common.out_channel := stdout;
        gen_one_file l
    | File f ->
        open_out_file f;
        gen_one_file l;
        close_out_file()
    | MultFiles ->
        gen_mult_files l

let produce_output fl =
  if List.length !prefs.compile_targets = 0 then
    produce_document fl
  else
    let otypes = !prefs.compile_targets in
    LatexCompiler.compile ~otypes ~produce_document fl

(*s \textbf{Main program.} Print the banner, parse the command line,
    read the files and then call [produce_document] from module [Web]. *)

let main ~prog args =
  CmdArgs.parse_args ~prog args; (* Sets prefs *)
  let files = List.rev !prefs.files in
  Index.init_coqlib_library ();
    if not !prefs.quiet then banner ();
    if files <> [] then produce_output files
