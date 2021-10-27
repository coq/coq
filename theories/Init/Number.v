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

Variant signed_int := IntDecimal (i:Decimal.int) | IntHexadecimal (i:Hexadecimal.int).
Notation int := signed_int.

Variant number := Decimal (d:Decimal.decimal) | Hexadecimal (h:Hexadecimal.hexadecimal).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for number.
Notation int_eq_dec := signed_int_eq_dec.
Notation int_beq := signed_int_beq.
Notation internal_int_dec_lb := internal_signed_int_dec_lb.
Notation internal_int_dec_bl := internal_signed_int_dec_bl.

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register number as num.number.type.

(** Pseudo-conversion functions used when declaring
    Number Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.
