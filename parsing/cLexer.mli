(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** This should be functional but it is not due to the interface *)
val add_keyword : ?quotation:starts_quotation -> string -> unit
val remove_keyword : string -> unit
val is_keyword : string -> bool
val keywords : unit -> CString.Set.t

type keyword_state
val set_keyword_state : keyword_state -> unit
val get_keyword_state : unit -> keyword_state

val check_ident : string -> unit
val is_ident : string -> bool
val check_keyword : string -> unit

(** When string is not an ident, returns a keyword. *)
val terminal : string -> string Tok.p

(** Precondition: the input is a numeral (c.f. [NumTok.t]) *)
val terminal_numeral : string -> NumTok.t Tok.p

(** The lexer of Coq: *)

module Lexer :
  Gramlib.Grammar.GLexerType with type te = Tok.t and type 'c pattern = 'c Tok.p

module Error : sig
  type t
  exception E of t
  val to_string : t -> string
end

(* Mainly for comments state, etc... *)
type lexer_state

val init_lexer_state : unit -> lexer_state
val set_lexer_state : lexer_state -> unit
val get_lexer_state : unit -> lexer_state
val drop_lexer_state : unit -> unit
val get_comment_state : lexer_state -> ((int * int) * string) list

(** Create a lexer.  true enables alternate handling for computing diffs.
It ensures that, ignoring white space, the concatenated tokens equal the input
string.  Specifically:
- for strings, return the enclosing quotes as tokens and treat the quoted value
as if it was unquoted, possibly becoming multiple tokens
- for comments, return the "(*" as a token and treat the contents of the comment as if
it was not in a comment, possibly becoming multiple tokens
- return any unrecognized Ascii or UTF-8 character as a string
*)
module LexerDiff :
  Gramlib.Grammar.GLexerType with type te = Tok.t and type 'c pattern = 'c Tok.p
