(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)




exception Syntax_error of string;;

let constraint_of_string s =
  let buf = Lexing.from_string s
  in
  try
      Poly_parser.constraint_entry Poly_lexer.token buf
  with
    | Parsing.Parse_error ->
	raise 
	  (Syntax_error 
	     ("Parse error in constraint_of_string, characters " ^ 
	      (string_of_int (Lexing.lexeme_start buf)) ^"-" ^ 
	      (string_of_int (Lexing.lexeme_end buf)) ))
    | Poly_lexer.Invalid_char s ->
	raise (Syntax_error ("Invalid char : " ^ s))
;;


let expr_of_string s =
  try
    let buf = Lexing.from_string s
    in
      Poly_parser.expr Poly_lexer.token buf
  with
      Parsing.Parse_error ->
	raise (Syntax_error "Parse error in expr_of_string")
  
