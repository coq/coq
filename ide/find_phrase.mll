{
  exception Lex_error of string
  let length = ref 0
  let buff = Buffer.create 513
}

rule next_phrase = parse
  | "(*" { incr length; incr length; 
	   skip_comment lexbuf;
	   next_phrase lexbuf}
  | '.'[' ''\n''\t''\r'] {	
      length := !length + 2; 
      Buffer.add_string buff (Lexing.lexeme lexbuf);
      Buffer.contents buff}
  | _ 
      { 
	let c = Lexing.lexeme_char lexbuf 0 in 
	if Ideutils.is_char_start c then incr length; 
	Buffer.add_char buff c ;
	next_phrase lexbuf
      }
  | eof  { raise (Lex_error "no phrase") }
and skip_comment = parse
  | "*)" {incr length; incr length; ()}
  | "(*" {incr length; incr length; 
	  skip_comment lexbuf;
	  skip_comment lexbuf}
  | _  { if Ideutils.is_char_start (Lexing.lexeme_char lexbuf 0) then 
	   incr length; 
	 skip_comment lexbuf}
  | eof  { raise (Lex_error "No closing *)") }


{
  let get lb = 
    Buffer.reset buff;
    length := 0;
    next_phrase lb

}
