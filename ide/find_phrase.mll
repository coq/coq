{
  exception Lex_error of string
  let length = ref 0
}

rule next_phrase = parse
  | "(*" { incr length; incr length; 
	   skip_comment lexbuf;
	   next_phrase lexbuf}
  | '.'[' ''\n''\t''\r'] {incr length; incr length; Lexing.lexeme lexbuf}
  | _ 
      { incr length; 
	let c = Lexing.lexeme lexbuf in c^(next_phrase lexbuf) 
      }
  | eof  { raise (Lex_error "no phrase") }
and skip_comment = parse
  | "*)" {incr length; incr length; ()}
  | "(*" {incr length; incr length; 
	  skip_comment lexbuf;
	  skip_comment lexbuf}
  | _  { incr length; skip_comment lexbuf}
  | eof  { raise (Lex_error "No closing *)") }
