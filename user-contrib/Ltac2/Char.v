(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Int.

Ltac2 @external of_int : int -> char := "rocq-runtime.plugins.ltac2" "char_of_int".
(** Throws if the integer is not a valid char (in range [0-255]). *)

Ltac2 @external to_int : char -> int := "rocq-runtime.plugins.ltac2" "char_to_int".

Ltac2 equal (x : char) (y : char) : bool := Int.equal (to_int x) (to_int y).
Ltac2 compare (x : char) (y : char) : int := Int.compare (to_int x) (to_int y).
