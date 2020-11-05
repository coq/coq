(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Deprecated: use Number.v instead *)

Require Import Decimal Hexadecimal Number.

#[deprecated(since="8.13",note="Use Number.uint instead.")]
Notation uint := uint (only parsing).
#[deprecated(since="8.13",note="Use Number.UintDecimal instead.")]
Notation UIntDec := UIntDecimal (only parsing).
#[deprecated(since="8.13",note="Use Number.UintHexadecimal instead.")]
Notation UIntHex := UIntHexadecimal (only parsing).

#[deprecated(since="8.13",note="Use Number.int instead.")]
Notation int := int (only parsing).
#[deprecated(since="8.13",note="Use Number.IntDecimal instead.")]
Notation IntDec := IntDecimal (only parsing).
#[deprecated(since="8.13",note="Use Number.IntHexadecimal instead.")]
Notation IntHex := IntHexadecimal (only parsing).

#[deprecated(since="8.13",note="Use Number.numeral instead.")]
Notation numeral := number (only parsing).
#[deprecated(since="8.13",note="Use Number.Decimal instead.")]
Notation Dec := Decimal (only parsing).
#[deprecated(since="8.13",note="Use Number.Hexadecimal instead.")]
Notation Hex := Hexadecimal (only parsing).

#[deprecated(since="8.13",note="Use Number.uint_beq instead.")]
Notation uint_beq := uint_beq (only parsing).
#[deprecated(since="8.13",note="Use Number.uint_eq_dec instead.")]
Notation uint_eq_dec := uint_eq_dec (only parsing).
#[deprecated(since="8.13",note="Use Number.int_beq instead.")]
Notation int_beq := int_beq (only parsing).
#[deprecated(since="8.13",note="Use Number.int_eq_dec instead.")]
Notation int_eq_dec := int_eq_dec (only parsing).
#[deprecated(since="8.13",note="Use Number.numeral_beq instead.")]
Notation numeral_beq := number_beq (only parsing).
#[deprecated(since="8.13",note="Use Number.numeral_eq_dec instead.")]
Notation numeral_eq_dec := number_eq_dec (only parsing).

Register number as num.numeral.type.

#[deprecated(since="8.13",note="Use Number.uint_of_uint instead.")]
Notation uint_of_uint := uint_of_uint (only parsing).
#[deprecated(since="8.13",note="Use Number.int_of_int instead.")]
Notation int_of_int := int_of_int (only parsing).
