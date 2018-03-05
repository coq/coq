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
  | EOI

val equal : t -> t -> bool
val extract_string : t -> string
val to_string : t -> string
(* Needed to fit Camlp5 signature *)
val print : Format.formatter -> t -> unit
val match_keyword : string -> t -> bool
(** for camlp5 *)
val of_pattern : string*string -> t
val to_pattern : t -> string*string
val match_pattern : string*string -> t -> string
