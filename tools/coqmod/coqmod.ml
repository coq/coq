(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqmodlib

let rec read_buffer t buf =
  match Lexer.parse_coq t buf with
  | t -> read_buffer t buf
  | exception Lexer.End_of_file -> t

let find_dependencies ~format f =
  let print =
    match !format with
    | "csexp" -> fun tok -> Token.to_sexp tok |> Csexp.to_channel stdout
    | "read" -> fun tok -> Printf.printf "%s\n" (Token.to_string tok)
    | "sexp" ->
        fun tok -> Token.to_sexp tok |> Token.Sexp.pp Format.std_formatter
    | f -> Error.unknwon_output_format f
  in
  let chan = try open_in f with Sys_error msg -> Error.cannot_open f msg in
  let buf = Lexing.from_channel chan in
  let t = Token.set_filename Token.empty f in
  let toks = read_buffer t buf in
  close_in chan; print (Token.sort_uniq toks)

let main () =
  let usage_msg = "coqmod - A simple module lexer for Coq" in
  let format = ref "csexp" in
  let files = ref [] in
  let anon_fun f = files := f :: !files in
  let speclist =
    [
      ("--format", Arg.Set_string format, "Set output format [csexp|sexp|read]");
      ("--debug", Arg.Set Error.debug_mode, "Output debugging information");
    ]
  in
  let () = Arg.parse speclist anon_fun usage_msg in
  match !files with
  | [] -> Error.no_file_provided ()
  | [file] -> find_dependencies ~format file
  | files -> Error.too_many_files_provided ()

let () =
  try main ()
  with exn ->
    Format.eprintf "@[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
