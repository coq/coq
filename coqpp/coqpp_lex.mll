(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{

open Lexing
open Coqpp_parse

type mode =
| OCaml
| Extend

exception Lex_error of Coqpp_ast.loc * string

let loc lexbuf = {
  Coqpp_ast.loc_start = lexeme_start_p lexbuf;
  Coqpp_ast.loc_end = lexeme_end_p lexbuf;
}

let newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  let pos = { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum } in
  lexbuf.lex_curr_p <- pos

let num_comments = ref 0
let num_braces = ref 0

let mode () = if !num_braces = 0 then Extend else OCaml

let comment_buf = Buffer.create 512
let ocaml_buf = Buffer.create 512
let string_buf = Buffer.create 512

let lex_error lexbuf msg =
  raise (Lex_error (loc lexbuf, msg))

let lex_unexpected_eof lexbuf where =
  lex_error lexbuf (Printf.sprintf "Unexpected end of file in %s" where)

let start_comment _ =
  let () = incr num_comments in
  Buffer.add_string comment_buf "(*"

let end_comment lexbuf =
  let () = decr num_comments in
  let () = Buffer.add_string comment_buf "*)" in
  if !num_comments < 0 then lex_error lexbuf "Unexpected end of comment"
  else if !num_comments = 0 then
    let s = Buffer.contents comment_buf in
    let () = Buffer.reset comment_buf in
    Some (COMMENT s)
  else
    None

let start_ocaml _ =
  let () = match mode () with
  | OCaml -> Buffer.add_string ocaml_buf "{"
  | Extend -> ()
  in
  incr num_braces

let end_ocaml lexbuf =
  let () = decr num_braces in
  if !num_braces < 0 then lex_error lexbuf "Unexpected end of OCaml code"
  else if !num_braces = 0 then
    let s = Buffer.contents ocaml_buf in
    let () = Buffer.reset ocaml_buf in
    Some (CODE { Coqpp_ast.code = s })
  else
    let () = Buffer.add_string ocaml_buf "}" in
    None

}

let letter = ['a'-'z' 'A'-'Z']
let letterlike = ['_' 'a'-'z' 'A'-'Z']
let alphanum = ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']
let ident = letterlike alphanum*
let qualid = ident ('.' ident)*
let space = [' ' '\t' '\r']
let number = [ '0'-'9' ]

rule extend = parse
| "(*" { start_comment (); comment lexbuf }
| "{" { start_ocaml (); ocaml lexbuf }
| "GRAMMAR" { GRAMMAR }
| "VERNAC" { VERNAC }
| "TACTIC" { TACTIC }
| "EXTEND" { EXTEND }
| "END" { END }
| "DECLARE" { DECLARE }
| "PLUGIN" { PLUGIN }
| "DEPRECATED" { DEPRECATED }
(** Camlp5 specific keywords *)
| "GLOBAL" { GLOBAL }
| "FIRST" { FIRST }
| "LAST" { LAST }
| "BEFORE" { BEFORE }
| "AFTER" { AFTER }
| "LEVEL" { LEVEL }
| "LEFTA" { LEFTA }
| "RIGHTA" { RIGHTA }
| "NONA" { NONA }
(** Standard *)
| ident { IDENT (Lexing.lexeme lexbuf) }
| qualid { QUALID (Lexing.lexeme lexbuf) }
| number { INT (int_of_string (Lexing.lexeme lexbuf)) }
| space { extend lexbuf }
| '\"' { string lexbuf }
| '\n' { newline lexbuf; extend lexbuf }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '|' { PIPE }
| "->" { ARROW }
| ',' { COMMA }
| ':' { COLON }
| ';' { SEMICOLON }
| '(' { LPAREN }
| ')' { RPAREN }
| '=' { EQUAL }
| _ { lex_error lexbuf "syntax error" }
| eof { EOF }

and ocaml = parse
| "{" { start_ocaml (); ocaml lexbuf }
| "}" { match end_ocaml lexbuf with Some tk -> tk | None -> ocaml lexbuf }
| '\n' { newline lexbuf; Buffer.add_char ocaml_buf '\n'; ocaml lexbuf }
| '\"' { Buffer.add_char ocaml_buf '\"'; ocaml_string lexbuf }
| (_ as c) { Buffer.add_char ocaml_buf c; ocaml lexbuf }
| eof { lex_unexpected_eof lexbuf "OCaml code" }

and comment = parse
| "*)" { match end_comment lexbuf with Some _ -> extend lexbuf | None -> comment lexbuf }
| "(*" { start_comment lexbuf; comment lexbuf }
| '\n' { newline lexbuf; Buffer.add_char comment_buf '\n'; comment lexbuf }
| (_ as c) { Buffer.add_char comment_buf c; comment lexbuf }
| eof { lex_unexpected_eof lexbuf "comment" }

and string = parse
| '\"'
  {
    let s = Buffer.contents string_buf in
    let () = Buffer.reset string_buf in
    STRING s
  }
| "\\\"" { Buffer.add_char string_buf '\"'; string lexbuf }
| '\n' { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
| (_ as c) { Buffer.add_char string_buf c; string lexbuf }
| eof { lex_unexpected_eof lexbuf "string" }

and ocaml_string = parse
| "\\\"" { Buffer.add_string ocaml_buf "\\\""; ocaml_string lexbuf }
| '\"' { Buffer.add_char ocaml_buf '\"'; ocaml lexbuf }
| (_ as c) { Buffer.add_char ocaml_buf c; ocaml_string lexbuf }
| eof { lex_unexpected_eof lexbuf "OCaml string" }

{

let token lexbuf = match mode () with
| OCaml -> ocaml lexbuf
| Extend -> extend lexbuf

}
