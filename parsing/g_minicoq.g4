
(* $Id$ *)

open Names
open Generic
open Term

let lexer = {
  Token.func = Lexer.func;
  Token.using = (fun _ -> ());
  Token.removing = (fun _ -> ());
  Token.tparse = Lexer.tparse;
  Token.text = Lexer.token_text }
  
let gram = Grammar.create lexer

let term = Grammar.Entry.create gram "term"
let command = Grammar.Entry.create gram "command"

EXTEND
  term: [ [ id = IDENT -> VAR (id_of_string id) ] ];
END

