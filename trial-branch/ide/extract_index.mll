(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

{
  open Lexing 
}

(* additional lexer to extract URL from Coq manual's index *)

rule entry = parse
  | "<LI><TT>" [^ ',']* "</TT>, "
      { let s = lexeme lexbuf in
	let n = String.length s in
	String.sub s 8 (n - 15), extract_index_url lexbuf }
  | "<LI>" [^ ',']* ", " 
      { let s = lexeme lexbuf in
	let n = String.length s in
	String.sub s 4 (n - 6), extract_index_url lexbuf }

and extract_index_url = parse
  | "<A HREF=\"" [^ '"']* '"'
      { let s = lexeme lexbuf in
	let n = String.length s in
	String.sub s 9 (n - 10) }
