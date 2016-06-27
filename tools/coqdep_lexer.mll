(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{

  open Filename
  open Lexing

  type mL_token = Use_module of string

  type qualid = string list

  type coq_token =
    | Require of qualid option * qualid list
    | Declare of string list
    | Load of string
    | AddLoadPath of string
    | AddRecLoadPath of string * qualid

  exception Fin_fichier
  exception Syntax_error of int*int

  let field_name s = String.sub s 1 (String.length s - 1)

  let unquote_string s =
    String.sub s 1 (String.length s - 2)

  let unquote_vfile_string s =
    let f = unquote_string s in
    if check_suffix f ".v" then chop_suffix f ".v" else f

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let syntax_error lexbuf =
    raise (Syntax_error (Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))
}

let space = [' ' '\t' '\n' '\r']
let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255']
let uppercase = ['A'-'Z' '\192'-'\214' '\216'-'\222']
let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let caml_up_ident = uppercase identchar*
let caml_low_ident = lowercase identchar*

let coq_firstchar =
  (* This is only an approximation, refer to lib/util.ml for correct def *)
  ['A'-'Z' 'a'-'z' '_'] |
  (* superscript 1 *)
  '\194' '\185' |
  (* utf-8 latin 1 supplement *)
  '\195' ['\128'-'\150'] | '\195' ['\152'-'\182'] | '\195' ['\184'-'\191'] |
  (* utf-8 letters *)
  '\206' (['\145'-'\161'] | ['\163'-'\187'])
  '\226' ('\130' [ '\128'-'\137' ] (* subscripts *)
    | '\129' [ '\176'-'\187' ] (* superscripts *)
    | '\132' ['\128'-'\191'] | '\133' ['\128'-'\143'])
let coq_identchar = coq_firstchar | ['\'' '0'-'9']
let coq_ident = coq_firstchar coq_identchar*
let coq_field = '.' coq_ident

let dot = '.' ( space+ | eof)

rule coq_action = parse
  | "Require" space+
      { require_modifiers None lexbuf }
  | "Local"? "Declare" space+ "ML" space+ "Module" space+
      { modules [] lexbuf }
  | "Load" space+
      { load_file lexbuf }
  | "Add" space+ "LoadPath" space+
      { add_loadpath lexbuf }
  | "Time" space+
      { coq_action lexbuf }
  | "Timeout" space+ ['0'-'9']+ space+
      { coq_action lexbuf }
  | "From" space+
      { from_rule lexbuf }
  | space+
      { coq_action lexbuf }
  | "(*"
      { comment lexbuf; coq_action lexbuf }
  | eof
      { raise Fin_fichier}
  | _
      { skip_to_dot lexbuf; coq_action lexbuf }

and from_rule = parse
  | "(*"
      { comment lexbuf; from_rule lexbuf }
  | space+
      { from_rule lexbuf }
  | coq_ident
      { let from = coq_qual_id_tail [Lexing.lexeme lexbuf] lexbuf in
        consume_require (Some from) lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and require_modifiers from = parse
  | "(*"
      { comment lexbuf; require_modifiers from lexbuf }
  | "Import" space+
      { require_file from lexbuf }
  | "Export" space+
      { require_file from lexbuf }
  | space+
      { require_modifiers from lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { backtrack lexbuf ; require_file from lexbuf }

and consume_require from = parse
  | "(*"
      { comment lexbuf; consume_require from lexbuf }
  | space+
      { consume_require from lexbuf }
  | "Require" space+
      { require_modifiers from lexbuf }
  | _
      { syntax_error lexbuf }

and add_loadpath = parse
  | "(*"
      { comment lexbuf; add_loadpath lexbuf }
  | space+
      { add_loadpath lexbuf }
  | eof
      { syntax_error lexbuf }
  | '"' [^ '"']* '"' (*'"'*)
      { add_loadpath_as (unquote_string (lexeme lexbuf)) lexbuf }

and add_loadpath_as path = parse
  | "(*"
      { comment lexbuf; add_loadpath_as path lexbuf }
  | space+
      { add_loadpath_as path lexbuf }
  | "as"
      { let qid = coq_qual_id lexbuf in
        skip_to_dot lexbuf;
        AddRecLoadPath (path, qid) }
  | dot
      { AddLoadPath path }

and caml_action = parse
  | space +
      { caml_action lexbuf }
  | "open" space* (caml_up_ident as id)
        { Use_module (String.uncapitalize id) }
  | "module" space+ caml_up_ident
        { caml_action lexbuf }
  | caml_low_ident { caml_action lexbuf }
  | caml_up_ident
      { qual_id (Lexing.lexeme lexbuf) lexbuf }
  | ['0'-'9']+
    | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
    | '0' ['o' 'O'] ['0'-'7']+
    | '0' ['b' 'B'] ['0'-'1']+
      { caml_action lexbuf }
  | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { caml_action lexbuf }
  | "\""
      { string lexbuf; caml_action lexbuf }
  | "'" [^ '\\' '\''] "'"
      { caml_action lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { caml_action lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { caml_action lexbuf }
  | "(*"
      { comment lexbuf; caml_action lexbuf }
  | "#" | "&"  | "&&" | "'" | "(" | ")" | "*" | "," | "?" | "->" | "." | ".."
   | ".(" | ".[" | ":" | "::" | ":=" | ";" | ";;" | "<-" | "=" | "[" | "[|"
   | "[<" | "]" | "_" | "{" | "|" | "||" | "|]" | ">]" | "}" | "!=" | "-"
   | "-."    { caml_action lexbuf }

  | ['!' '?' '~']
    ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] *
            { caml_action lexbuf }
  | ['=' '<' '>' '@' '^' '|' '&' '$']
    ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] *
            { caml_action lexbuf }
  | ['+' '-']
    ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] *
            { caml_action lexbuf }
  | "**"
    ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] *
            { caml_action lexbuf }
  | ['*' '/' '%']
    ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~'] *
            { caml_action lexbuf }
  | eof { raise Fin_fichier }
  | _ { caml_action lexbuf }

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

and string = parse
  | '"' (* '"' *)
      { () }
  | '\\' ("\010" | "\013" | "\010\013") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"' 'n' 't' 'b' 'r'] (*'"'*)
      { string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { string lexbuf }
  | eof
      { raise Fin_fichier }
  | _
      { string lexbuf }

and load_file = parse
  | '"' [^ '"']* '"' (*'"'*)
      { let s = lexeme lexbuf in
	parse_dot lexbuf;
	Load (unquote_vfile_string s) }
  | coq_ident
      { let s = lexeme lexbuf in skip_to_dot lexbuf; Load s }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and require_file from = parse
  | "(*"
      { comment lexbuf; require_file from lexbuf }
  | space+
      { require_file from lexbuf }
  | coq_ident
      { let name = coq_qual_id_tail [Lexing.lexeme lexbuf] lexbuf in
        let qid = coq_qual_id_list [name] lexbuf in
        parse_dot lexbuf;
        Require (from, qid) }
  | eof
      { syntax_error lexbuf }
  | _
      { syntax_error lexbuf }

and skip_to_dot = parse
  | dot { () }
  | eof { syntax_error lexbuf }
  | _   { skip_to_dot lexbuf }

and parse_dot = parse
  | dot { () }
  | eof { syntax_error lexbuf }
  | _ { syntax_error lexbuf }

and coq_qual_id = parse
  | "(*"
      { comment lexbuf; coq_qual_id lexbuf }
  | space+
      { coq_qual_id lexbuf }
  | coq_ident
      { coq_qual_id_tail [Lexing.lexeme lexbuf] lexbuf }
  | _
      { syntax_error lexbuf }

and coq_qual_id_tail module_name = parse
  | "(*"
      { comment lexbuf; coq_qual_id_tail module_name lexbuf }
  | space+
      { coq_qual_id_tail module_name lexbuf }
  | coq_field
      { coq_qual_id_tail (field_name (Lexing.lexeme lexbuf) :: module_name) lexbuf }
  | eof
      { syntax_error lexbuf }
  | _
      { backtrack lexbuf;
        List.rev module_name }

and coq_qual_id_list module_names = parse
  | "(*"
      { comment lexbuf; coq_qual_id_list module_names lexbuf }
  | space+
      { coq_qual_id_list module_names lexbuf }
  | coq_ident
      { let name = coq_qual_id_tail [Lexing.lexeme lexbuf] lexbuf in
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

and qual_id ml_module_name = parse
  | '.' [^ '.' '(' '[']
      { Use_module (String.uncapitalize ml_module_name) }
  | eof { raise Fin_fichier }
  | _ { caml_action lexbuf }

and mllib_list = parse
  | caml_up_ident { let s = String.uncapitalize (Lexing.lexeme lexbuf)
		in s :: mllib_list lexbuf }
  | "*predef*" { mllib_list lexbuf }
  | space+ { mllib_list lexbuf }
  | eof { [] }
  | _ { syntax_error lexbuf }

and ocamldep_parse = parse
  | [^ ':' ]* ':' { mllib_list lexbuf }
