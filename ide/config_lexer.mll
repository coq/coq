(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{

  open Lexing
  open Format
  open Config_parser
  open Util

  let string_buffer = Buffer.create 1024

}

let space = [' ' '\010' '\013' '\009' '\012']
let char = ['A'-'Z' 'a'-'z' '_' '0'-'9']
let ident = char+

rule token = parse
  | space+        { token lexbuf }
  | '#' [^ '\n']* { token lexbuf }
  | ident { IDENT (lexeme lexbuf) }
  | '='   { EQUAL }
  | '"'   { Buffer.reset string_buffer;
	    Buffer.add_char string_buffer '"';
	    string lexbuf;
	    let s = Buffer.contents string_buffer in
	    STRING (Scanf.sscanf s "%S" (fun s -> s)) }
  | _     { let c = lexeme_start lexbuf in
	    eprintf ".coqiderc: invalid character (%d)\n@." c;
	    token lexbuf }
  | eof   { EOF }

and string = parse
  | '"'  { Buffer.add_char string_buffer '"' }
  | '\\' '"' | _
         { Buffer.add_string string_buffer (lexeme lexbuf); string lexbuf }
  | eof  { eprintf ".coqiderc: unterminated string\n@." }

{

  let load_file f =
    let c = open_in f in
    let lb = from_channel c in
    let m = Config_parser.prefs token lb in
    close_in c;
    m

  let print_file f m =
    let c = open_out f in
    let fmt = formatter_of_out_channel c in
    let rec print_list fmt = function
      | [] -> ()
      | s :: sl -> fprintf fmt "%S@ %a" s print_list sl
    in
    Stringmap.iter
      (fun k s -> fprintf fmt "@[<hov 2>%s = %a@]@\n" k print_list s) m;
    fprintf fmt "@.";
    close_out c

}
