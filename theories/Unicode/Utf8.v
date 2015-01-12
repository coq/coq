(* -*- coding:utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
