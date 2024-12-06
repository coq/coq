(* -*- coding:utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Utf8_core.

(* Arithmetic *)
Notation "x ≤ y" := (le x y) (at level 70, no associativity).
Notation "x ≥ y" := (ge x y) (at level 70, no associativity).

(* test *)
(*
Check ∀ x z, True -> (∃ y v, x + v ≥ y + z) ∨ x ≤ 0.
*)

(* Integer Arithmetic *)
(* TODO: this should come after ZArith
Notation "x ≤ y" := (Z.le x y) (at level 70, no associativity).
*)
