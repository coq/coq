(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

rule rocq_string = parse
  | "\"\"" { rocq_string lexbuf }
  | "\"" { () }
  | eof { () }
  | utf8_extra_byte { incr utf8_adjust; rocq_string lexbuf }
  | _ { rocq_string lexbuf }

and comment = parse
  | "(*" { let _  = comment lexbuf in comment lexbuf }
  | "\"" { let () = rocq_string lexbuf in comment lexbuf }
  | "*)" { Some (utf8_lexeme_start lexbuf) }
  | eof { None }
  | utf8_extra_byte { incr utf8_adjust; comment lexbuf }
  | _ { comment lexbuf }

and quotation n l = parse
| eof { raise Unterminated }
| utf8_extra_byte { incr utf8_adjust; quotation n l lexbuf }
| "{" { quotation_nesting n l 1 lexbuf }
| "}" { quotation_closing n l 1 lexbuf }
| _ { quotation n l lexbuf }

and quotation_nesting n l v = parse
| eof { raise Unterminated }
| utf8_extra_byte { incr utf8_adjust; quotation n l lexbuf }
| "{" {
  if n = v+1 then quotation n (l+1) lexbuf
  else quotation_nesting n l (v+1) lexbuf
}
| "}" { quotation_closing n l 1 lexbuf }
| _ { quotation n l lexbuf }

and quotation_closing n l v = parse
| eof { raise Unterminated }
| utf8_extra_byte { incr utf8_adjust; quotation n l lexbuf }
| "}" {
  if n = v+1 then
    if l = 1 then ()
    else quotation n (l-1) lexbuf
  else quotation_closing n l (v+1) lexbuf
}
| "{" { quotation_nesting n l 1 lexbuf }
| _ { quotation n l lexbuf }

and quotation_start n = parse
| eof { raise Unterminated }
| utf8_extra_byte { incr utf8_adjust; quotation n 1 lexbuf }
| "{" { quotation_start (n+1) lexbuf }
| _ { quotation n 1 lexbuf }

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
      let () = rocq_string lexbuf in
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
  | ['a'-'z' 'A'-'Z'] ":{{" {
      quotation_start 2 lexbuf;
      sentence false stamp lexbuf
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
