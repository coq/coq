
{
 open Lexing
 open Syntax

 let chan_out = ref stdout

 let comment_depth = ref 0
 let print s = output_string !chan_out s
 
 exception Fin_fichier

}

let space = [' ' '\t' '\n']
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']

let identifier = letter (letter | digit | ['_' '\''])*
let number = digit+
let oper = ['-' '+' '/' '*' '|' '>' '<' '=' '%' '#' '$' ':' '\\' '?'
            '.' '!' '@' ]+

rule token = parse
  | "let" {LET}
  | "in" {IN}
  | "match" {MATCH}
  | "with" {WITH}
  | "end" {END}
  | "and" {AND}
  | "fun" {FUN}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "eval" {EVAL}
  | "for" {FOR}
  | "Prop" {PROP}
  | "Set" {SET}
  | "Type" {TYPE}
  | "fix" {FIX}
  | "cofix" {COFIX}
  | "struct" {STRUCT}
  | "as" {AS}

  | "Simpl" {SIMPL}

  | "_" {WILDCARD}
  | "(" {LPAR}
  | ")" {RPAR}
  | "{" {LBRACE}
  | "}" {RBRACE}
  | "!" {BANG}
  | "@" {AT}
  | ":" {COLON}
  | ":=" {COLONEQ}
  | "." {DOT}
  | "," {COMMA}
  | "->" {OPER "->"}
  | "=>" {RARROW}
  | "|" {BAR}
  | "%" {PERCENT}

  | '?' { META(ident lexbuf)}
  | number { INT(Lexing.lexeme lexbuf) }
  | oper { OPER(Lexing.lexeme lexbuf) }
  | identifier { IDENT (Lexing.lexeme lexbuf) }
  | "(*" (*"*)"*)       { comment_depth := 1;
                          comment lexbuf;
		          token lexbuf }
  | space+     { token lexbuf}
  | eof        { EOF }

and ident = parse
  | identifier { Lexing.lexeme lexbuf }

and comment = parse
  | "(*" (*"*)"*)  { incr comment_depth; comment lexbuf }
  | (*"(*"*) "*)"
      { decr comment_depth; if !comment_depth > 0 then comment lexbuf }
  | eof   { raise Fin_fichier } 
  | _     { comment lexbuf }
