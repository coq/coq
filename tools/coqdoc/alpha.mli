(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Alphabetic order. *)

val compare_char : char -> char -> int
val compare_string : string -> string -> int

(* Alphabetic normalization. *)

val norm_char : char -> char
val norm_string : string -> string
