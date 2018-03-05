(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Unicode utilities *)

type status

(** Classify a unicode char into 3 classes or unknown. *)
val classify : int -> status

(** Return [None] if a given string can be used as a (Coq) identifier.
    Return [Some (b,s)] otherwise, where [s] is an explanation and [b] is severity. *)
val ident_refutation : string -> (bool * string) option

(** Tells if a valid initial character for an identifier *)
val is_valid_ident_initial : status -> bool

(** Tells if a valid non-initial character for an identifier *)
val is_valid_ident_trailing : status -> bool

(** Tells if a character is unclassified *)
val is_unknown : status -> bool

(** First char of a string, converted to lowercase
    @raise Assert_failure if the input string is empty. *)
val lowercase_first_char : string -> string

(** Split a string supposed to be an ident at the first letter;
    as an optimization, return None if the first character is a letter *)
val split_at_first_letter : string -> (string * string) option

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

(** Return a "%XX"-escaped string if it contains non UTF-8 characters. *)
val escaped_if_non_utf8 : string -> string
