(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Import Ltac2.Int.

Ltac2 @external of_int : int -> char := "ltac2" "char_of_int".
Ltac2 @external to_int : char -> int := "ltac2" "char_to_int".

Ltac2 equal (x : char) (y : char) : bool :=
  Int.equal (Char.to_int x) (Char.to_int y).
