(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Unicode utilities *)

type status = Letter | IdentPart | Symbol

exception Unsupported

(** Classify a unicode char into 3 classes, or raise [Unsupported] *)
val classify : int -> status

(** Check whether a given string be used as a legal identifier.
    - [None] means yes
    - [Some (b,s)] means no, with explanation [s] and severity [b] *)
val ident_refutation : string -> (bool * string) option

(** First char of a string, converted to lowercase *)
val lowercase_first_char : string -> string

(** For extraction, turn a unicode string into an ascii-only one *)
val is_basic_ascii : string -> bool
val ascii_of_ident : string -> string
