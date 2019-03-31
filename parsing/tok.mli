(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

type t =
  | KEYWORD of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | QUOTATION of string * string
  | EOI

val equal : t -> t -> bool
(* pass true for diff_mode *)
val extract_string : bool -> t -> string
val to_string : t -> string
(* Needed to fit Camlp5 signature *)
val print : Format.formatter -> t -> unit
val match_keyword : string -> t -> bool

(** Utility function for the test returned by a QUOTATION token:
    It returns the delimiter parenthesis, if any, and the text
    without delimiters. Eg `{{{ text }}}` -> Some '{', ` text ` *)
val trim_quotation : string -> char option * string

(** for camlp5,
    eg GRAMMAR EXTEND ..... [ IDENT "x" -> .... END
    is a pattern ("IDENT", Some "x")
*)
type pattern = string * string option (* = Plexing.pattern *)

val is_keyword : pattern -> (bool * string) option
val pattern_for_EOI : pattern
val pattern_for_KEYWORD : string -> pattern
val pattern_for_IDENT : string -> pattern
val match_pattern : pattern -> t -> string
