type token =
    IDENT of (string)
  | PARGAUCHE
  | PARDROITE
  | SEMICOLON
  | COMMA
  | EOF
  | TRUE
  | FALSE
  | AND
  | OR
  | NOT
  | IMPLIES
  | EQUIV
  | EXISTS
  | FORALL
  | PLUS
  | MINUS
  | EXP
  | MULT
  | DIV
  | VERTICALBAR
  | COMP of (string)
  | INT of (Numbers.t)

val constraint_entry :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Abstract_constraint.formula
val expr :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Abstract_constraint.expr
