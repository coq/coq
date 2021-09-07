(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

type 'c p =
  | PKEYWORD : string -> string p
  | PPATTERNIDENT : string option -> string p
  | PIDENT : string option -> string p
  | PFIELD : string option -> string p
  | PNUMBER : NumTok.Unsigned.t option -> NumTok.Unsigned.t p
  | PSTRING : string option -> string p
  | PLEFTQMARK : unit p
  | PBULLET : string option -> string p
  | PQUOTATION : string -> string p
  | PEOI : unit p

val pattern_strings : 'c p -> string * string option

type t =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | NUMBER of NumTok.Unsigned.t
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | QUOTATION of string * string
  | EOI

val equal_p : 'a p -> 'b p -> ('a, 'b) Util.eq option

val equal : t -> t -> bool
(* pass true for diff_mode *)
val extract_string : bool -> t -> string

(** Names of tokens, used in Grammar error messages *)

val token_text : 'c p -> string

(** Utility function for the test returned by a QUOTATION token:
    It returns the delimiter parenthesis, if any, and the text
    without delimiters. Eg `{{{ text }}}` -> Some '{', ` text ` *)
val trim_quotation : string -> char option * string

(** for camlp5,
    eg GRAMMAR EXTEND ..... [ IDENT "x" -> .... END
    is a pattern (PIDENT (Some "x"))
*)
val match_pattern : 'c p -> t -> 'c
