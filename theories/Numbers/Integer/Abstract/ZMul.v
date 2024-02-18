(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export ZAdd.

Module ZMulProp (Import Z : ZAxiomsMiniSig').
Include ZAddProp Z.

(** A note on naming: right (correspondingly, left) distributivity
    happens when the sum is multiplied by a number on the right
    (left), not when the sum itself is the right (left) factor in the
    product (see planetmath.org and mathworld.wolfram.com). In the old
    library BinInt, distributivity over subtraction was named
    correctly, but distributivity over addition was named
    incorrectly. The names in Isabelle/HOL library are also
    incorrect. *)

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Theorem mul_opp_l : forall n m, (- n) * m == - (n * m).
Proof.
intros n m. apply add_move_0_r.
now rewrite <- mul_add_distr_r, add_opp_diag_l, mul_0_l.
Qed.

Theorem mul_opp_r : forall n m, n * (- m) == - (n * m).
Proof.
intros n m; rewrite (mul_comm n (- m)), (mul_comm n m); apply mul_opp_l.
Qed.

Theorem mul_opp_opp : forall n m, (- n) * (- m) == n * m.
Proof.
intros n m; now rewrite mul_opp_l, mul_opp_r, opp_involutive.
Qed.

Theorem mul_opp_comm : forall n m, (- n) * m == n * (- m).
Proof.
intros n m. now rewrite mul_opp_l, <- mul_opp_r.
Qed.

End ZMulProp.


