(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

{
  exception Lex_error of string
  let length = ref 0
  let buff = Buffer.create 513

}

let phrase_sep = '.'

rule next_phrase = parse
  | "(*" { incr length; incr length; 
	   skip_comment lexbuf;
	   next_phrase lexbuf}
  | '"'[^'"']*'"' { let lexeme = Lexing.lexeme lexbuf in 
		 let ulen = Glib.Utf8.length lexeme in
		 length := !length + ulen;
		 Buffer.add_string buff lexeme;
		 next_phrase lexbuf
	       }
  | phrase_sep[' ''\n''\t''\r'] {
      length := !length + 2; 
      Buffer.add_string buff (Lexing.lexeme lexbuf);
      Buffer.contents buff}

  | phrase_sep eof{
      length := !length + 1; 
      Buffer.add_string buff (Lexing.lexeme lexbuf);
      Buffer.contents buff}
  | phrase_sep phrase_sep
      { 
	length := !length + 2; 
	Buffer.add_string buff (Lexing.lexeme lexbuf);
	next_phrase lexbuf
      }
  | _ 
      { 
	let c = Lexing.lexeme_char lexbuf 0 in 
	if Ideutils.is_char_start c then incr length; 
	Buffer.add_char buff c ;
	next_phrase lexbuf
      }
  | eof  { raise (Lex_error "Phrase should end with . followed by a separator") }
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
