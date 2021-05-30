(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decimal or Hexadecimal numbers *)

Require Import Decimal Hexadecimal.

Variant uint := UIntDecimal (u:Decimal.uint) | UIntHexadecimal (u:Hexadecimal.uint).
#[deprecated(since="8.13",note="Use UintDecimal instead.")]
Notation UIntDec := UIntDecimal (only parsing).
#[deprecated(since="8.13",note="Use UintHexadecimal instead.")]
Notation UIntHex := UIntHexadecimal (only parsing).

Variant int := IntDecimal (i:Decimal.int) | IntHexadecimal (i:Hexadecimal.int).
#[deprecated(since="8.13",note="Use IntDecimal instead.")]
Notation IntDec := IntDecimal (only parsing).
#[deprecated(since="8.13",note="Use IntHexadecimal instead.")]
Notation IntHex := IntHexadecimal (only parsing).

Variant number := Decimal (d:Decimal.decimal) | Hexadecimal (h:Hexadecimal.hexadecimal).
#[deprecated(since="8.13",note="Use Decimal instead.")]
Notation Dec := Decimal (only parsing).
#[deprecated(since="8.13",note="Use Hexadecimal instead.")]
Notation Hex := Hexadecimal (only parsing).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for number.

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register number as num.number.type.

(** Pseudo-conversion functions used when declaring
    Number Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.
