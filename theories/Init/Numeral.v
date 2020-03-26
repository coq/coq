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

Variant uint := UIntDec (u:Decimal.uint) | UIntHex (u:Hexadecimal.uint).

Variant int := IntDec (i:Decimal.int) | IntHex (i:Hexadecimal.int).

Variant numeral := Dec (d:Decimal.decimal) | Hex (h:Hexadecimal.hexadecimal).

Scheme Equality for uint.
Scheme Equality for int.
Scheme Equality for numeral.

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register numeral as num.numeral.type.

(** Pseudo-conversion functions used when declaring
    Numeral Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.
