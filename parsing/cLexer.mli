(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** When one registers a keyword she can declare it starts a quotation.
  In particular using QUOTATION("name:") in a grammar rule
  declares "name:" as a keyword and the token QUOTATION is
  matched whenever the keyword is followed by an identifier or a
  parenthesized text. Eg

    constr:x
    string:[....]
    ltac:(....)
    ltac:{....}

  The delimiter is made of 1 or more occurrences of the same parenthesis,
  eg ((.....)) or [[[[....]]]]. The idea being that if the text happens to
  contain the closing delimiter, one can make the delimiter longer and avoid
  confusion (no escaping). Eg

    string:[[ .. ']' .. ]]


  Nesting the delimiter is allowed, eg ((..((...))..)) is OK.

  Keywords don't need to end in ':' *)
type starts_quotation = NoQuotation | Quotation

type keyword_state

val empty_keyword_state : keyword_state

val add_keyword : ?quotation:starts_quotation -> keyword_state -> string -> keyword_state

val is_keyword : keyword_state -> string -> bool
val keywords : keyword_state -> CString.Set.t

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit

val add_keyword_tok : keyword_state -> 'c Tok.p -> keyword_state

(** When string is not an ident, returns a keyword. *)
val terminal : keyword_state -> string -> string Tok.p

(** Precondition: the input is a number (c.f. [NumTok.t]) *)
val terminal_number : string -> NumTok.Unsigned.t Tok.p

(** [after loc] Will advance a lexing location as the lexer does; this
    can be used to implement parsing resumption from a given position:
{[
  let loc = Procq.Parsable.loc pa |> after in
  let str = Gramlib.Stream.of_string text in
  (* Stream.count being correct is critical for Rocq's lexer *)
  Gramlib.Stream.njunk loc.ep str;
  let pa = Procq.Parsable.make ~loc str in
  (* ready to resume parsing *)
]}
*)
val after : Loc.t -> Loc.t

(** The lexer of Rocq: *)

module Lexer :
  Gramlib.Plexing.S
  with type keyword_state = keyword_state
   and type te = Tok.t
   and type 'c pattern = 'c Tok.p


module Error : sig
  type t
  exception E of t
  val to_string : t -> string
end

(** LexerDiff ensures that, ignoring white space, the concatenated
    tokens equal the input string. Specifically:
    - for strings, return the enclosing quotes as tokens and treat the
      quoted value as if it was unquoted, possibly becoming multiple
      tokens.
    - for comments, return the "(\*" (\ to be kind to syntax
      highlighters) as a token and treat the contents of the comment as
      if it was not in a comment, possibly becoming multiple tokens.
    - return any unrecognized Ascii or UTF-8 character as a string.
*)

module LexerDiff :
  Gramlib.Plexing.S
  with type keyword_state = keyword_state
   and type te = Tok.t
   and type 'c pattern = 'c Tok.p
