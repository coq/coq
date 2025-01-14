(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Numbers in different forms: signed or unsigned, possibly with
    fractional part and exponent.

    Numbers are represented using raw strings of (hexa)decimal
    literals and a separate sign flag.

    Note that this representation is not unique, due to possible
    multiple leading or trailing zeros, and -0 = +0, for instances.
    The reason to keep the number exactly as it was parsed is that
    specific notations can be declared for specific numbers
    (e.g. [Notation "0" := False], or [Notation "00" := (nil,nil)], or
    [Notation "2e1" := ...]). Those notations override the generic
    interpretation as number. So, one has to record the form of the
    number which exactly matches the notation. *)

type sign = SPlus | SMinus

type num_class = CDec | CHex

type 'a exp = EDec of 'a | EBin of 'a

(** {6 String representation of a natural number } *)

module UnsignedNat :
sig
  type t
  val of_string : string -> t
    (** Convert from a non-empty sequence of digits (which may contain "_")
        (or hexdigits when starting with "0x" or "0X") *)

  val to_string : t -> string
    (** Convert to a non-empty sequence of digit that does not contain "_"
        (or hexdigits, starting with "0x", all hexdigits are lower case) *)

  val sprint : t -> string
  val print : t -> Pp.t
    (** [sprint] and [print] returns the number as it was parsed, for printing *)

  val classify : t -> num_class

  val compare : t -> t -> int
end

(** {6 String representation of a signed natural number } *)

module SignedNat :
sig
  type t = sign * UnsignedNat.t
  val of_string : string -> t
    (** Convert from a non-empty sequence of (hex)digits which may contain "_" *)

  val to_string : t -> string
    (** Convert to a non-empty sequence of (hex)digit that does not contain "_"
        (hexadecimals start with "0x" and all hexdigits are lower case) *)

  val classify : t -> num_class

  val of_bigint : num_class -> Z.t -> t
  val to_bigint : t -> Z.t
end

(** {6 Unsigned decimal numbers } *)

module Unsigned :
sig
  type t
  val equal : t -> t -> bool
  val is_nat : t -> bool
  val to_nat : t -> string option

  val sprint : t -> string
  val print : t -> Pp.t
    (** [sprint] and [print] returns the number as it was parsed, for printing *)

  val parse : (unit,char) Gramlib.Stream.t -> t
    (** Parse a positive Rocq number.
        Precondition: the first char on the stream is already known to be a digit (\[0-9\]).
        Precondition: at least two extra chars after the number to parse.

        The recognized syntax is:
        - integer part: \[0-9\]\[0-9_\]*
        - fractional part: empty or .\[0-9_\]+
        - exponent part: empty or \[eE\]\[+-\]?\[0-9\]\[0-9_\]*
        or
        - integer part: 0\[xX\]\[0-9a-fA-F\]\[0-9a-fA-F_\]*
        - fractional part: empty or .\[0-9a-fA-F_\]+
        - exponent part: empty or \[pP\]\[+-\]?\[0-9\]\[0-9_\]* *)

  val parse_string : string -> t option
    (** Parse the string as a non negative Rocq number, if possible *)

  val classify : t -> num_class

end

(** {6 Signed decimal numbers } *)

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
    (** [sprint] and [print] returns the number as it was parsed, for printing *)

  val parse_string : string -> t option
    (** Parse the string as a signed Rocq number, if possible *)

  val of_int_string : string -> t
    (** Convert from a string in the syntax of OCaml's int/int64 *)

  val of_string : string -> t
    (** Convert from a string in the syntax of OCaml's string_of_float *)

  val to_string : t -> string
    (** Returns a string in the syntax of OCaml's float_of_string *)

  val of_bigint : num_class -> Z.t -> t
  val to_bigint : t -> Z.t option
    (** Convert from and to bigint when the denotation of a bigint *)

  val of_int_frac_and_exponent : SignedNat.t -> UnsignedNat.t option -> SignedNat.t option -> t
  val to_int_frac_and_exponent : t -> SignedNat.t * UnsignedNat.t option * SignedNat.t option
    (** n, p and q such that the number is n.p*10^q or n.p*2^q
        pre/postcondition: classify n = classify p, classify q = CDec *)

  val of_bigint_and_exponent : Z.t -> Z.t exp -> t
  val to_bigint_and_exponent : t -> Z.t * Z.t exp
    (** n and p such that the number is n*10^p or n*2^p *)

  val classify : t -> num_class

  val is_bigger_int_than : t -> UnsignedNat.t -> bool
    (** Test if an integer whose absolute value is bounded *)

end
