(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
{
 
  (* $Id: *)
  
  open Lexing
   
  type mL_token = Use_module of string

  type spec = bool
		
  type coq_token = 
    | Require of spec * string
    | RequireString of spec * string
    | Declare of string list

  let mlAccu  = ref ([] : (string * string * string option) list) 
  and mliAccu = ref ([] : (string * string * string option) list) 
  and vAccu   = ref ([] : (string * string option) list)

  let mlKnown     = ref ([] : (string * string option) list) 
  and mliKnown    = ref ([] : (string * string option) list) 
  and vKnown      = ref ([] : (string * string option) list) 
  and coqlibKnown = ref ([] : (string * string option) list)

  let coqlib = ref Coq_config.coqlib
		 
  let (dep_tab : (string,string list) Hashtbl.t) = Hashtbl.create 151
						     
  let addQueue q v = q := v :: !q
		       
  let file_name = function
    | (s,None)     -> s 
    | (s,Some ".") -> s
    | (s,Some d)   -> Filename.concat d s

  let comment_depth = ref 0
 
  exception Fin_fichier
    
  let module_name = ref ""
		      
  let specif = ref false
		 
  let mllist = ref ([] : string list)
}

let space = [' ' '\t' '\n']
let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255']
let uppercase = ['A'-'Z' '\192'-'\214' '\216'-'\222']
let identchar = 
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let coq_ident = ['a'-'z' '_' '0'-'9' 'A'-'Z']+

rule coq_action = parse
  | "Require" space+
      { specif := false; opened_file lexbuf }
  | "Require" space+ "Export" space+
      { specif := false; opened_file lexbuf}
  | "Require" space+ "Syntax" space+
      { specif := false; opened_file lexbuf}
  | "Require" space+ "Import" space+
      { specif := false; opened_file lexbuf}
  | "Declare" space+ "ML" space+ "Module" space+
      { mllist := []; modules lexbuf}
  | "\""
      { string lexbuf; coq_action lexbuf}
  | "(*"
      { comment_depth := 1; comment lexbuf; coq_action lexbuf }  
  | eof { raise Fin_fichier} 
  | _   { coq_action lexbuf }

and caml_action = parse
  | [' ' '\010' '\013' '\009' '\012'] +
      { caml_action lexbuf }
  | "open" [' ' '\010' '\013' '\009' '\012']*
        { caml_opened_file lexbuf }
  | lowercase identchar*
      { caml_action lexbuf }
  | uppercase identchar*
      { module_name := Lexing.lexeme lexbuf;
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
  | "(*"
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
  | "(*"
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
  | '"'
      { () }
  | '\\' ("\010" | "\013" | "\010\013") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"' 'n' 't' 'b' 'r']
      { string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { string lexbuf }
  | eof
      { raise Fin_fichier }
  | _
      { string lexbuf }

and opened_file = parse
  | "(*"  	{ comment_depth := 1; comment lexbuf; opened_file lexbuf }
  | space+
      	       	{ opened_file lexbuf }
  | "Implementation"
                { opened_file lexbuf }
  | "Specification"
                { specif := true; opened_file lexbuf }
  | coq_ident
       	       	{ module_name := (Lexing.lexeme lexbuf);
                  opened_file_end lexbuf }

and opened_file_end = parse
  | '.'               { Require (!specif, !module_name) }
  | space+            { opened_file_end lexbuf }
  | "(*"              { comment_depth := 1; comment lexbuf;
      	       	       	opened_file_end lexbuf }
  | '"' [^'"']* '"'   { let lex = Lexing.lexeme lexbuf in
      	       	       	let str = String.sub lex 1 (String.length lex - 2) in
			RequireString (!specif, str) }
  | eof		      { raise Fin_fichier }
  | _		      { opened_file_end lexbuf }

and modules = parse
  | space+              { modules lexbuf }
  | "(*"		{ comment_depth := 1; comment lexbuf;
      	       	       	  modules lexbuf }
  | '"' [^'"']* '"'
        { let lex = (Lexing.lexeme lexbuf) in 
	  let str = String.sub lex 1 (String.length lex - 2) in
	  mllist := str :: !mllist; modules lexbuf }
  | _   { (Declare (List.rev !mllist)) }   

and qual_id = parse
  | '.' [^ '.' '(' '['] { Use_module (String.uncapitalize !module_name) }
  | eof { raise Fin_fichier }
  | _ { caml_action lexbuf }

and caml_opened_file = parse
  | uppercase identchar*
      { let lex = (Lexing.lexeme lexbuf) in 
        let str = String.sub lex 0 (String.length lex) in
        (Use_module (String.uncapitalize str)) }
  | eof {raise Fin_fichier }
  | _ { caml_action lexbuf }



