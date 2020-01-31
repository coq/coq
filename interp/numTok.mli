(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Numerals in different forms: signed or unsigned, possibly with
    fractional part and exponent.

    Numerals are represented using raw strings of decimal
    literals and a separate sign flag.

    Note that this representation is not unique, due to possible
    multiple leading or trailing zeros, and -0 = +0, for instances.
    The reason to keep the numeral exactly as it was parsed is that
    specific notations can be declared for specific numerals
    (e.g. [Notation "0" := False], or [Notation "00" := (nil,nil)], or
    [Notation "2e1" := ...]). Those notations override the generic
    interpretation as numeral. So, one has to record the form of the
    numeral which exactly matches the notation. *)

type sign = SPlus | SMinus

(** {6 String representation of a natural number } *)

module UnsignedNat :
sig
  type t
  val of_string : string -> t
    (** Convert from a non-empty sequence of digits (which may contain "_") *)

  val to_string : t -> string
    (** Convert to a non-empty sequence of digit that does not contain "_" *)

  val sprint : t -> string
  val print : t -> Pp.t
    (** [sprint] and [print] returns the numeral as it was parsed, for printing *)

  val compare : t -> t -> int
end

(** {6 String representation of a signed natural number } *)

module SignedNat :
sig
  type t = sign * UnsignedNat.t
  val of_string : string -> t
    (** Convert from a non-empty sequence of digits which may contain "_" *)

  val to_string : t -> string
    (** Convert to a non-empty sequence of digit that does not contain "_" *)

  val to_bigint : t -> Bigint.bigint
  val of_bigint : Bigint.bigint -> t
end

(** {6 Unsigned decimal numerals } *)

module Unsigned :
sig
  type t
  val equal : t -> t -> bool
  val is_nat : t -> bool
  val to_nat : t -> string option

  val sprint : t -> string
  val print : t -> Pp.t
    (** [sprint] and [print] returns the numeral as it was parsed, for printing *)

  val parse : char Stream.t -> t
    (** Parse a positive Coq numeral.
        Precondition: the first char on the stream is already known to be a digit (\[0-9\]).
        Precondition: at least two extra chars after the numeral to parse.

        The recognized syntax is:
        - integer part: \[0-9\]\[0-9_\]*
        - decimal part: empty or .\[0-9_\]+
        - exponent part: empty or \[eE\]\[+-\]?\[0-9\]\[0-9_\]* *)

  val parse_string : string -> t option
    (** Parse the string as a positive Coq numeral, if possible *)

end

(** {6 Signed decimal numerals } *)

module Signed :
sig
  type t = sign * Unsigned.t
  val equal : t -> t -> bool
  val is_zero : t -> bool
  val of_nat : UnsignedNat.t -> t
  val of_int : SignedNat.t -> t
  val to_int : t -> SignedNat.t option
  val is_int : t -> bool

  val sprint : t -> string
  val print : t -> Pp.t
    (** [sprint] and [print] returns the numeral as it was parsed, for printing *)

  val parse_string : string -> t option
    (** Parse the string as a signed Coq numeral, if possible *)

  val of_int_string : string -> t
    (** Convert from a string in the syntax of OCaml's int/int64 *)

  val of_string : string -> t
    (** Convert from a string in the syntax of OCaml's string_of_float *)

  val to_string : t -> string
    (** Returns a string in the syntax of OCaml's float_of_string *)

  val of_bigint : Bigint.bigint -> t
  val to_bigint : t -> Bigint.bigint option
    (** Convert from and to bigint when the denotation of a bigint *)

  val of_decimal_and_exponent : SignedNat.t -> UnsignedNat.t option -> SignedNat.t option -> t
  val to_decimal_and_exponent : t -> SignedNat.t * UnsignedNat.t option * SignedNat.t option
    (** n, p and q such that the number is n.p*10^q *)

  val to_bigint_and_exponent : t -> Bigint.bigint * Bigint.bigint
  val of_bigint_and_exponent : Bigint.bigint -> Bigint.bigint -> t
    (** n and p such that the number is n*10^p *)

  val is_bigger_int_than : t -> UnsignedNat.t -> bool
    (** Test if an integer whose absolute value is bounded *)

end
