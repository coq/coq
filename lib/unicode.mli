(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Unicode utilities *)

type status = Letter | IdentPart | Symbol | Unknown

(** Classify a unicode char into 3 classes or unknown. *)
val classify : int -> status

(** Return [None] if a given string can be used as a (Coq) identifier.
    Return [Some (b,s)] otherwise, where [s] is an explanation and [b] is severity. *)
val ident_refutation : string -> (bool * string) option

(** First char of a string, converted to lowercase
    @raise Assert_failure if the input string is empty. *)
val lowercase_first_char : string -> string

(** Return [true] if all UTF-8 characters in the input string are just plain
    ASCII characters. Returns [false] otherwise. *)
val is_basic_ascii : string -> bool

(** [ascii_of_ident s] maps UTF-8 string to a string composed solely from ASCII
    characters. The non-ASCII characters are translated to ["_UUxxxx_"] where
    {i xxxx} is the Unicode index of the character in hexadecimal (from four
    to six hex digits). To avoid potential name clashes, any preexisting
    substring ["_UU"] is turned into ["_UUU"]. *)
val ascii_of_ident : string -> string

(** Validate an UTF-8 string *)
val is_utf8 : string -> bool

(** Return the length of a valid UTF-8 string. *)
val utf8_length : string -> int

(** Variant of {!String.sub} for UTF-8 strings. *)
val utf8_sub : string -> int -> int -> string
