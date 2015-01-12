(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The type of token for the Coq lexer and parser *)

type t =
  | KEYWORD of string
  | METAIDENT of string
  | PATTERNIDENT of string
  | IDENT of string
  | FIELD of string
  | INT of string
  | STRING of string
  | LEFTQMARK
  | BULLET of string
  | EOI

val extract_string : t -> string
val to_string : t -> string
(* Needed to fit Camlp4 signature *)
val print : Format.formatter -> t -> unit
val match_keyword : string -> t -> bool
(** for camlp5 *)
val of_pattern : string*string -> t
val to_pattern : t -> string*string
val match_pattern : string*string -> t -> string
