(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

{
type markup =
  | Comment of (int*int)
  | String of (int*int)
  | SentenceEnd of int

}

let ws = [' ' '\010' '\013' '\009' '\012']

let sentence_sep = '.' [ ' ' '\n' '\t']

rule coq_string = parse
  | "\"\"" { coq_string lexbuf }
  | "\"" { Lexing.lexeme_end lexbuf }
  | _ { coq_string lexbuf }
  | eof { Lexing.lexeme_end lexbuf }

and comment = parse
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | "*)" { Lexing.lexeme_end lexbuf }
  | "\"" { ignore (coq_string lexbuf); comment lexbuf }
  | _ { comment lexbuf }
  | eof { Lexing.lexeme_end lexbuf }

and sentence tag_cb = parse
  | ws+ { sentence tag_cb lexbuf }
  | _ { sentence tag_cb lexbuf }
  | ".." { sentence tag_cb lexbuf }
  | "(*" {
      let comm_start = Lexing.lexeme_start lexbuf in
      let comm_end = comment lexbuf in
      tag_cb (Comment (comm_start,comm_end));
      sentence tag_cb lexbuf }
  | "\"" {
      let str_start = Lexing.lexeme_start lexbuf in
      let str_end = coq_string lexbuf in
      tag_cb (String (str_start,str_end));
      sentence tag_cb lexbuf }
  | eof { raise Not_found } 
  | sentence_sep {
        tag_cb (SentenceEnd (Lexing.lexeme_end lexbuf))
    }

{
  let parse tag_cb slice =
    let lb = Lexing.from_string slice in
    sentence tag_cb lb;
    Lexing.lexeme_end lb
}
