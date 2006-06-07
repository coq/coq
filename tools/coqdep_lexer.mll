(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)
  
{

  open Filename 
  open Lexing
   
  type mL_token = Use_module of string

  type spec = bool
		
  type coq_token = 
    | Require of spec * string list list
    | RequireString of spec * string
    | Declare of string list
    | Load of string

  let comment_depth = ref 0
 
  exception Fin_fichier
    
  let module_current_name = ref []
  let module_names = ref []
  let ml_module_name = ref ""
		      
  let specif = ref false
		 
  let mllist = ref ([] : string list)

  let field_name s = String.sub s 1 (String.length s - 1)
}

let space = [' ' '\t' '\n' '\r']
let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255']
let uppercase = ['A'-'Z' '\192'-'\214' '\216'-'\222']
let identchar = 
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let coq_ident = ['a'-'z' '_' '0'-'9' 'A'-'Z']+
let coq_field = '.'['a'-'z' '_' '0'-'9' 'A'-'Z']+
let dot = '.' ( space+ | eof)

rule coq_action = parse
  | "Require" space+
      { specif := false; module_names := []; opened_file lexbuf }
  | "Require" space+ "Export" space+
      { specif := false; module_names := []; opened_file lexbuf}
  | "Require" space+ "Import" space+
      { specif := false; module_names := []; opened_file lexbuf}
  | "Declare" space+ "ML" space+ "Module" space+
      { mllist := []; modules lexbuf}
  | "Load" space+
      { load_file lexbuf }
  | "\""
      { string lexbuf; coq_action lexbuf}
  | "(*" (* "*)" *)
      { comment_depth := 1; comment lexbuf; coq_action lexbuf }  
  | eof 
      { raise Fin_fichier} 
  | _   
      { coq_action lexbuf }

and caml_action = parse
  | [' ' '\010' '\013' '\009' '\012'] +
      { caml_action lexbuf }
  | "open" [' ' '\010' '\013' '\009' '\012']*
        { caml_opened_file lexbuf }
  | lowercase identchar*
      { caml_action lexbuf }
  | uppercase identchar*
      { ml_module_name := Lexing.lexeme lexbuf;
        qual_id lexbuf }
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
  | "(*" (* "*)" *)
      { comment_depth := 1; comment lexbuf; caml_action lexbuf }
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
  | "(*" (* "*)" *)
      { comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { raise Fin_fichier } 
  | _ { comment lexbuf }

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
	let f = String.sub s 1 (String.length s - 2) in
	skip_to_dot lexbuf;
	Load (if check_suffix f ".v" then chop_suffix f ".v" else f) }
  | coq_ident
      { let s = lexeme lexbuf in skip_to_dot lexbuf; Load s }
  | eof	
      { raise Fin_fichier }
  | _
      { load_file lexbuf }

and skip_to_dot = parse
  | dot { () }
  | eof { () }
  | _   { skip_to_dot lexbuf }

and opened_file = parse
  | "(*" (* "*)" *) { comment_depth := 1; comment lexbuf; opened_file lexbuf }
  | space+
      	       	{ opened_file lexbuf }
  | "Implementation"
                { opened_file lexbuf }
  | "Specification"
                { specif := true; opened_file lexbuf }
  | coq_ident
       	       	{ module_current_name := [Lexing.lexeme lexbuf];
                  opened_file_fields lexbuf }

  | '"' [^'"']* '"'   { (*'"'*)
                        let lex = Lexing.lexeme lexbuf in
      	       	       	let str = String.sub lex 1 (String.length lex - 2) in
                        let str =
                          if Filename.check_suffix str ".v" then
                            Filename.chop_suffix str ".v"
                          else str in
			RequireString (!specif, str) }
  | eof         { raise Fin_fichier }
  | _           { opened_file lexbuf }

and opened_file_fields = parse
  | "(*" (* "*)" *)
                { comment_depth := 1; comment lexbuf;
                  opened_file_fields lexbuf }
  | space+
                { opened_file_fields lexbuf }
  | coq_field
                { module_current_name :=
                    field_name (Lexing.lexeme lexbuf) :: !module_current_name;
                  opened_file_fields lexbuf }
  | coq_ident   { module_names := 
                    List.rev !module_current_name :: !module_names;
                  module_current_name := [Lexing.lexeme lexbuf];
                  opened_file_fields lexbuf }
  | dot         { module_names :=
                    List.rev !module_current_name :: !module_names;
                  Require (!specif, List.rev !module_names) }
  | eof         { raise Fin_fichier }
  | _           { opened_file_fields lexbuf }

and modules = parse
  | space+              { modules lexbuf }
  | "(*" (* "*)" *)	{ comment_depth := 1; comment lexbuf;
      	       	       	  modules lexbuf }
  | '"' [^'"']* '"'
        { let lex = (Lexing.lexeme lexbuf) in 
	  let str = String.sub lex 1 (String.length lex - 2) in
	  mllist := str :: !mllist; modules lexbuf }
  | _   { (Declare (List.rev !mllist)) }   

and qual_id = parse
  | '.' [^ '.' '(' '['] { Use_module (String.uncapitalize !ml_module_name) }
  | eof { raise Fin_fichier }
  | _ { caml_action lexbuf }

and caml_opened_file = parse
  | uppercase identchar*
      { let lex = (Lexing.lexeme lexbuf) in 
        let str = String.sub lex 0 (String.length lex) in
        (Use_module (String.uncapitalize str)) }
  | eof {raise Fin_fichier }
  | _ { caml_action lexbuf }



