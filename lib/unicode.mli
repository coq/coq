(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Unicode utilities *)

type status = Letter | IdentPart | Symbol

(** This exception is raised when UTF-8 the input string contains unsupported UTF-8 characters. *)
exception Unsupported

(** Classify a unicode char into 3 classes.
    @raise Unsupported if the input string contains unsupported UTF-8 characters. *)
val classify : int -> status

(** Return [None] if a given string can be used as a (Coq) identifier.
    Return [Some (b,s)] otherwise, where [s] is an explanation and [b] is severity.
    @raise Unsupported if the input string contains unsupported UTF-8 characters. *)
val ident_refutation : string -> (bool * string) option

(** First char of a string, converted to lowercase
    @raise Unsupported if the input string contains unsupported UTF-8 characters.
    @raise Assert_failure if the input string is empty. *)
val lowercase_first_char : string -> string

(** Return [true] if all UTF-8 characters in the input string are just plain ASCII characters.
    Returns [false] otherwise. *)
val is_basic_ascii : string -> bool

(** [ascii_of_ident s] maps UTF-8 string to a string composed solely from ASCII characters.
    Those UTF-8 characters which do not have their ASCII counterparts are
    translated to ["__Uxxxx_"] where {i xxxx} are four hexadecimal digits.
    @raise Unsupported if the input string contains unsupported UTF-8 characters. *)
val ascii_of_ident : string -> string

(** Validate an UTF-8 string *)
val is_utf8 : string -> bool
