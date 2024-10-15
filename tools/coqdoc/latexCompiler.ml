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

let locally dir f x =
  let cwd = Sys.getcwd () in
  try
    Sys.chdir dir;
    let y = f x in
    Sys.chdir cwd; y
  with e -> Sys.chdir cwd; raise e

let clean_temp_files basefile =
  let remove f = try Sys.remove f with _ -> () in
  remove (basefile ^ ".tex");
  remove (basefile ^ ".log");
  remove (basefile ^ ".aux");
  remove (basefile ^ ".toc");
  remove (basefile ^ ".dvi");
  remove (basefile ^ ".ps");
  remove (basefile ^ ".pdf");
  remove (basefile ^ ".haux");
  remove (basefile ^ ".html")

let clean_and_exit file res = clean_temp_files file; exit res

let cat file =
  let c = open_in file in
  try
    while true do
      print_char (input_char c)
    done
  with End_of_file -> close_in c

let compile ~otypes ~produce_document fl =
  let texfile = Filename.temp_file "coqdoc" ".tex" in
  let basefile = Filename.chop_suffix texfile ".tex" in
  let final_out_to = !prefs.out_to in
  prefs := { !prefs with out_to = File texfile };
  prefs := { !prefs with output_dir = Filename.dirname texfile };  produce_document fl;
  let latexexe = if List.mem Pdf otypes then "pdflatex" else "latex" in
  let latexcmd =
    let file = Filename.basename texfile in
    let file =
      if !prefs.quiet then sprintf "'\\nonstopmode\\input{%s}'" file else file
    in
    sprintf "%s %s && %s %s 1>&2 %s" latexexe file latexexe file
      (if !prefs.quiet then "> /dev/null" else "")
  in
  let res = locally (Filename.dirname texfile) Sys.command latexcmd in
  if res <> 0 then begin
    eprintf "Couldn't run LaTeX successfully\n";
    clean_and_exit basefile res
  end;
  let dvifile = basefile ^ ".dvi" in
  ( if List.mem Dvi otypes then
    match final_out_to with
    | MultFiles | StdOut -> cat dvifile
    | File f -> FileUtil.copy dvifile f );
  let pdffile = basefile ^ ".pdf" in
  ( if List.mem Pdf otypes then
    match final_out_to with
    | MultFiles | StdOut -> cat pdffile
    | File f -> FileUtil.copy pdffile f );
  if List.mem Ps otypes then begin
    let psfile = basefile ^ ".ps" in
    let command =
      sprintf "dvips %s -o %s %s" dvifile psfile
        (if !prefs.quiet then "> /dev/null 2>&1" else "")
    in
    let res = Sys.command command in
    if res <> 0 then begin
      eprintf "Couldn't run dvips successfully\n";
      clean_and_exit basefile res
    end;
    match final_out_to with
    | MultFiles | StdOut -> cat psfile
    | File f -> FileUtil.copy psfile f
  end;
  clean_temp_files basefile
