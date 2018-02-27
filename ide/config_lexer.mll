(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

{

  open Lexing
  open Format

  let string_buffer = Buffer.create 1024

}

let space = [' ' '\010' '\013' '\009' '\012']
let char = ['A'-'Z' 'a'-'z' '_' '0'-'9']
let ident = (char | '.')+
let ignore = space | ('#' [^ '\n']*)

rule prefs m = parse
  |ignore* (ident as id) ignore* '=' { let conf = str_list [] lexbuf in
				 prefs (Util.String.Map.add id conf m) lexbuf }
  | _     { let c = lexeme_start lexbuf in
	      eprintf "coqiderc: invalid character (%d)\n@." c;
	      prefs m lexbuf }
  | eof   { m }

and str_list l = parse
  | ignore* '"'   { Buffer.reset string_buffer;
		    Buffer.add_char string_buffer '"';
		    string lexbuf;
		    let s = Buffer.contents string_buffer in
		      str_list ((Scanf.sscanf s "%S" (fun s -> s))::l) lexbuf }
  |ignore+ { List.rev l}

and string = parse
  | '"'  { Buffer.add_char string_buffer '"' }
  | '\\' '"' | _
         { Buffer.add_string string_buffer (lexeme lexbuf); string lexbuf }
  | eof  { eprintf "coqiderc: unterminated string\n@." }

{

  let load_file f =
    let c = open_in f in
    let lb = from_channel c in
    let m = prefs Util.String.Map.empty lb in
    close_in c;
    m

  let print_file f m =
    let c = open_out f in
    let fmt = formatter_of_out_channel c in
    let rec print_list fmt = function
      | [] -> ()
      | s :: sl -> fprintf fmt "%S@ %a" s print_list sl
    in
    Util.String.Map.iter
      (fun k s -> fprintf fmt "@[<hov 2>%s = %a@]@\n" k print_list s) m;
    fprintf fmt "@.";
    close_out c

}
