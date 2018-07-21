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
  exception Unterminated

  let utf8_adjust = ref 0

  let utf8_lexeme_start lexbuf =
    Lexing.lexeme_start lexbuf - !utf8_adjust
}

let space = [' ' '\n' '\r' '\t' '\012'] (* '\012' is form-feed *)

let number = [ '0'-'9' ]+

let string = "\"" _+ "\""

let alpha = ['a'-'z' 'A'-'Z']

let ident = alpha (alpha | number | '_' | "'")*

let undotted_sep = ((number | '[' ident ']') space* ':' space*)? '{' | '}' | '-'+ | '+'+ | '*'+

let vernac_control = "Fail" | "Time" | "Redirect" space+ string | "Timeout" space+ number

let dot_sep = '.' (space | eof)

let utf8_extra_byte = [ '\x80' - '\xBF' ]

rule coq_string = parse
  | "\"\"" { coq_string lexbuf }
  | "\"" { () }
  | eof { () }
  | utf8_extra_byte { incr utf8_adjust; coq_string lexbuf }
  | _ { coq_string lexbuf }

and comment = parse
  | "(*" { let _  = comment lexbuf in comment lexbuf }
  | "\"" { let () = coq_string lexbuf in comment lexbuf }
  | "*)" { Some (utf8_lexeme_start lexbuf) }
  | eof { None }
  | utf8_extra_byte { incr utf8_adjust; comment lexbuf }
  | _ { comment lexbuf }

(** NB : [mkiter] should be called on increasing offsets *)

and sentence initial stamp = parse
  | "(*" {
      match comment lexbuf with
        | None -> raise Unterminated
        | Some comm_last ->
          stamp comm_last Tags.Script.comment;
          sentence initial stamp lexbuf
    }
  | "\"" {
      let () = coq_string lexbuf in
      sentence false stamp lexbuf
    }
  | ".." {
      (* We must have a particular rule for parsing "..", where no dot
	 is a terminator, even if we have a blank afterwards
	 (cf. for instance the syntax for recursive notation).
	 This rule and the following one also allow to treat the "..."
	 special case, where the third dot is a terminator. *)
      sentence false stamp lexbuf
    }
  | dot_sep {
      (* The usual "." terminator *)
      stamp (utf8_lexeme_start lexbuf) Tags.Script.sentence;
      sentence true stamp lexbuf
    }
  | (vernac_control space+)* undotted_sep {
      (* Separators like { or } and bullets * - + are only active
	 at the start of a sentence *)
      if initial then stamp (utf8_lexeme_start lexbuf + String.length (Lexing.lexeme lexbuf) - 1) Tags.Script.sentence;
      sentence initial stamp lexbuf
    }
  | space+ {
       (* Parsing spaces is the only situation preserving initiality *)
       sentence initial stamp lexbuf
    }
  | utf8_extra_byte { incr utf8_adjust; sentence false stamp lexbuf }
  | eof { if initial then () else raise Unterminated }
  | _ {
      (* Any other characters *)
      sentence false stamp lexbuf
    }

{

  (** Parse sentences in string [slice], tagging last characters
      of sentences with the [stamp] function.
      It will raise [Unterminated] if [slice] ends with an unfinished
      sentence.
  *)

  let delimit_sentences stamp slice =
    utf8_adjust := 0;
    sentence true stamp (Lexing.from_string slice)

}
