(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

{

  open Filename
  open Lexing

  type qualid = string list

  type load = Logical of string | Physical of string

  type coq_token =
    | Require of qualid option * qualid list
    | Declare of string list
    | Load of load
    | External of qualid * string

  exception Fin_fichier
  exception Syntax_error of int*int

  let unquote_string s =
    String.sub s 1 (String.length s - 2)

  let unquote_vfile_string s =
    let f = unquote_string s in
    if check_suffix f ".v" then chop_suffix f ".v" else f

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let syntax_error lexbuf =
    raise (Syntax_error (Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))

  let check_valid lexbuf s =
    match Unicode.ident_refutation s with
    | None -> s
    | Some _ -> syntax_error lexbuf

  let get_ident lexbuf =
    let s = Lexing.lexeme lexbuf in check_valid lexbuf s

  let get_field_name lexbuf =
    let s = Lexing.lexeme lexbuf in
    check_valid lexbuf (String.sub s 1 (String.length s - 1))

}

let space = [' ' '\t' '\n' '\r']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let caml_up_ident = uppercase identchar*
let caml_low_ident = lowercase identchar*

(* This is an overapproximation, we check correctness afterwards *)
let coq_ident = ['A'-'Z' 'a'-'z' '_' '\128'-'\255'] ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9' '\128'-'\255']*
let coq_field = '.' coq_ident
let coq_qual_id_rex = coq_ident coq_field+

let dot = '.' ( space+ | eof)

rule coq_action = parse
  | "Require" space+
      { require_modifiers None lexbuf }
  | "Local" space+ "Declare" space+ "ML" space+ "Module" space+
      { modules [] lexbuf }
  | "Declare" space+ "ML" space+ "Module" space+
      { modules [] lexbuf }
  | "Load" space+
      { load_file lexbuf }
  | "Time" space+
      { coq_action lexbuf }
  | "Timeout" space+ ['0'-'9']+ space+
      { coq_action lexbuf }
  | "From" space+
      { from_rule false lexbuf }
  | "Comments" space+ "From" space+
      { from_rule true lexbuf }
  | "#["
      { skip_attribute lexbuf; coq_action lexbuf }
  | space+
      { coq_action lexbuf }
  | "(*"
      { comment lexbuf; coq_action lexbuf }
  | eof
      { raise Fin_fichier}
  | _
      { skip_to_dot lexbuf; coq_action lexbuf }

and skip_attribute = parse
  | "(*"
      { comment lexbuf; skip_attribute lexbuf }
  | "]"
      { () }
  | '"' [^ '"']* '"'
      { skip_attribute lexbuf }
  | _
      { skip_attribute lexbuf }

and from_rule only_extra_dep = parse
  | "(*"
      { comment lexbuf; from_rule only_extra_dep lexbuf }
  | space+
      { from_rule only_extra_dep lexbuf }
  | coq_ident
      { let from = coq_qual_id_tail [get_ident lexbuf] lexbuf in
        consume_require_or_extradeps only_extra_dep (Some from) lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and extra_dep_rule from = parse
  | "(*"
      { comment lexbuf; extra_dep_rule from lexbuf }
  | space+
      { extra_dep_rule from lexbuf }
  | eof
      { syntax_error lexbuf }
  | '"' ([^ '"']+ as f) '"' (*'"'*)
      { skip_to_dot lexbuf;
        External (from,f) }

and require_modifiers from = parse
  | "(*"
      { comment lexbuf; require_modifiers from lexbuf }
  | "Import" space*
      { require_file from lexbuf }
  | "Export" space*
      { require_file from lexbuf }
  | space+
      { require_modifiers from lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { backtrack lexbuf ; require_file from lexbuf }

and consume_require_or_extradeps only_extra_dep from = parse
  | "(*"
      { comment lexbuf; consume_require_or_extradeps only_extra_dep from lexbuf }
  | space+
      { consume_require_or_extradeps only_extra_dep from lexbuf }
  | "Require" space+
      { if only_extra_dep then syntax_error lexbuf; require_modifiers from lexbuf }
  | "Extra" space+ "Dependency" space+
      { match from with
        | None -> syntax_error lexbuf (* Extra Dependency requires From *)
        | Some from -> extra_dep_rule from lexbuf }
  | _
      { syntax_error lexbuf }

and comment = parse
  | "(*"
      { comment lexbuf; comment lexbuf }
  | "*)"
      { () }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { raise Fin_fichier }
  | _
      { comment lexbuf }

and skip_parenthesized = parse
  | "(*"
      { comment lexbuf; skip_parenthesized lexbuf }
  | "("
      { skip_parenthesized lexbuf; skip_parenthesized lexbuf }
  | ")"
      { () }
  | eof
      { raise Fin_fichier }
  | _
    { skip_parenthesized lexbuf }

and load_file = parse
  | '"' [^ '"']* '"' (*'"'*)
      { let s = lexeme lexbuf in
        parse_dot lexbuf;
        Load (Physical (unquote_vfile_string s)) }
  | coq_ident
      { let s = get_ident lexbuf in skip_to_dot lexbuf; Load (Logical s) }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and require_file from = parse
  | "(*"
      { comment lexbuf; require_file from lexbuf }
  | ("-" space*)? "("
    { skip_parenthesized lexbuf; require_file from lexbuf }
  | space+
      { require_file from lexbuf }
  | coq_ident
      { let name = coq_qual_id_tail [get_ident lexbuf] lexbuf in
        let qid = coq_qual_id_list [name] lexbuf in
        parse_dot lexbuf;
        Require (from, qid) }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and skip_to_dot = parse
  | "(*"
      { comment lexbuf; skip_to_dot lexbuf }
  | dot { () }
  | eof { syntax_error lexbuf }
  | _   { skip_to_dot lexbuf }

and parse_dot = parse
  | dot { () }
  | eof { syntax_error lexbuf }
  | _ { syntax_error lexbuf }

and coq_qual_id_tail module_name = parse
  | "(*"
      { comment lexbuf; coq_qual_id_tail module_name lexbuf }
  | space+
      { coq_qual_id_tail module_name lexbuf }
  | coq_field
      { coq_qual_id_tail (get_field_name lexbuf :: module_name) lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { backtrack lexbuf;
        List.rev module_name }

and coq_qual_id_list module_names = parse
  | "(*"
      { comment lexbuf; coq_qual_id_list module_names lexbuf }
  | "("
    { skip_parenthesized lexbuf; coq_qual_id_list module_names lexbuf }
  | space+
      { coq_qual_id_list module_names lexbuf }
  | coq_ident
      { let name = coq_qual_id_tail [get_ident lexbuf] lexbuf in
        coq_qual_id_list (name :: module_names) lexbuf
      }
  | eof
      { syntax_error lexbuf }
  | _
      { backtrack lexbuf;
        List.rev module_names }

and modules mllist = parse
  | space+
      { modules mllist lexbuf }
  | "(*"
      { comment lexbuf; modules mllist lexbuf }
  | '"' [^'"']* '"'
      { let lex = (Lexing.lexeme lexbuf) in
        let str = String.sub lex 1 (String.length lex - 2) in
        modules (str :: mllist) lexbuf}
  | eof
      { syntax_error lexbuf }
  | _
      { Declare (List.rev mllist) }
