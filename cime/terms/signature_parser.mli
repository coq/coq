type token =
    IDENT of (string)
  | INT of (string)
  | COMMA
  | COLON
  | SEMICOLON
  | KW_PREFIX
  | KW_INFIX
  | KW_POSTFIX
  | KW_C
  | KW_AC
  | KW_CONSTANT
  | KW_UNARY
  | KW_BINARY
  | EOF
  | AS
  | ARROW

val signature :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> (string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) list
val sorted_signature :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> ((string list * int * Signatures.symbol_fix * Signature_syntax.symbol_theory) * ((string list * string)list)) list 
