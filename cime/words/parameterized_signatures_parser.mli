type token =
    FORMULA of (string)
  | SEMICOLON
  | PIPE
  | IDENT of (string)
  | EOF
  | POWER
  | FP
  | LPAR
  | RPAR
  | ARROW

val signature_eof :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parameterized_signatures_syntax.signature
val cword_eof :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parameterized_signatures_syntax.constrained_word
val rules_eof :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parameterized_signatures_syntax.rules
