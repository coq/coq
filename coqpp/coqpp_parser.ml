(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Lexing
open Coqpp_ast

let pr_loc loc =
  let file = loc.loc_start.pos_fname in
  let line = loc.loc_start.pos_lnum in
  let bpos = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
  let epos = loc.loc_end.pos_cnum - loc.loc_start.pos_bol in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:" file line bpos epos


let fatal msg =
  let () = Format.eprintf "Error: %s@\n%!" msg in
  exit 1

let parse_file f =
  let chan = open_in f in
  let lexbuf = Lexing.from_channel chan in
  let () = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = f } in
  let ans =
    try Coqpp_parse.file Coqpp_lex.token lexbuf
    with
    | Coqpp_lex.Lex_error (loc, msg) ->
      let () = close_in chan in
      let () = Printf.eprintf "%s\n%!" (pr_loc loc) in
      fatal msg
    | Parsing.Parse_error ->
      let () = close_in chan in
      let loc = Coqpp_lex.loc lexbuf in
      let () = Printf.eprintf "%s\n%!" (pr_loc loc) in
      fatal "syntax error"
  in
  let () = close_in chan in
  ans
