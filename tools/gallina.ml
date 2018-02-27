(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Gallina_lexer

let vfiles = ref ([] : string list)

let option_moins = ref false

let option_stdout = ref false

let traite_fichier f =
  try
    let chan_in = open_in (f^".v") in
    let buf = Lexing.from_channel chan_in in
    if not !option_stdout then chan_out := open_out (f ^ ".g");
    try
      while true do Gallina_lexer.action buf done
    with Fin_fichier -> begin
      flush !chan_out;
      close_in chan_in;
      if not !option_stdout then close_out !chan_out
    end
  with Sys_error _ ->
    ()

let traite_stdin () =
  try
    let buf = Lexing.from_channel stdin in
    try
      while true do Gallina_lexer.action buf done
    with Fin_fichier ->
      flush !chan_out
  with Sys_error _ ->
    ()

let _ =
  let lg_command = Array.length Sys.argv in
  if lg_command < 2 then begin
    output_string stderr "Usage: gallina [-] [-stdout] file1 file2 ...\n";
    flush stderr;
    exit 1
  end;
  let treat = function
    | "-" -> option_moins := true
    | "-stdout" -> option_stdout := true
    | "-nocomments" -> comments := false
    | f ->
	if Filename.check_suffix f ".v" then
       	  vfiles := (Filename.chop_suffix f ".v") :: !vfiles
  in
  Array.iter treat Sys.argv;
  if !option_moins then
    traite_stdin ()
  else
    List.iter traite_fichier !vfiles
