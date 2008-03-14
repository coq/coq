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
  let b = Buffer.create 127

}

(* Replace all occurences of \x{iiii} and \x{iiiiiiii} by UTF-8 valid chars *)

let digit = ['0'-'9''A'-'Z''a'-'z']
let short = digit digit digit digit
let long = short short

rule entry = parse
  | "\\x{" (short | long ) '}'
      { let s = lexeme lexbuf in
	let n = String.length s in
	let code = 
	  try Glib.Utf8.from_unichar 
	    (int_of_string ("0x"^(String.sub s 3 (n - 4)))) 
	  with _ -> s
	in
	let c = if Glib.Utf8.validate code then code else s in
	Buffer.add_string b c;
	entry lexbuf
      }
  | _ 
      { let s = lexeme lexbuf in
	Buffer.add_string b s;
	entry lexbuf}
  | eof
      {
	let s = Buffer.contents b in Buffer.reset b ; s
      }


{
  let f s =
   let lb = from_string s in
   Buffer.reset b;
   entry lb
}
