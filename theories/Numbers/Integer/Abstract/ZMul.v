(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export ZAdd.

Module ZMulPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZAddPropMod := ZAddPropFunct ZAxiomsMod.
Open Local Scope IntScope.

Theorem Zmul_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> n1 * m1 == n2 * m2.
Proof NZmul_wd.

Theorem Zmul_0_l : forall n : Z, 0 * n == 0.
Proof NZmul_0_l.

Theorem Zmul_succ_l : forall n m : Z, (S n) * m == n * m + m.
Proof NZmul_succ_l.

(* Theorems that are valid for both natural numbers and integers *)

Theorem Zmul_0_r : forall n : Z, n * 0 == 0.
Proof NZmul_0_r.

Theorem Zmul_succ_r : forall n m : Z, n * (S m) == n * m + n.
Proof NZmul_succ_r.

Theorem Zmul_comm : forall n m : Z, n * m == m * n.
Proof NZmul_comm.

Theorem Zmul_add_distr_r : forall n m p : Z, (n + m) * p == n * p + m * p.
Proof NZmul_add_distr_r.

Theorem Zmul_add_distr_l : forall n m p : Z, n * (m + p) == n * m + n * p.
Proof NZmul_add_distr_l.

(* A note on naming: right (correspondingly, left) distributivity happens
when the sum is multiplied by a number on the right (left), not when the
sum itself is the right (left) factor in the product (see planetmath.org
and mathworld.wolfram.com). In the old library BinInt, distributivity over
subtraction was named correctly, but distributivity over addition was named
incorrectly. The names in Isabelle/HOL library are also incorrect. *)

Theorem Zmul_assoc : forall n m p : Z, n * (m * p) == (n * m) * p.
Proof NZmul_assoc.

Theorem Zmul_1_l : forall n : Z, 1 * n == n.
Proof NZmul_1_l.

Theorem Zmul_1_r : forall n : Z, n * 1 == n.
Proof NZmul_1_r.

(* The following two theorems are true in an ordered ring,
but since they don't mention order, we'll put them here *)

Theorem Zeq_mul_0 : forall n m : Z, n * m == 0 <-> n == 0 \/ m == 0.
Proof NZeq_mul_0.

Theorem Zneq_mul_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZneq_mul_0.

(* Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zmul_pred_r : forall n m : Z, n * (P m) == n * m - n.
Proof.
intros n m.
rewrite <- (Zsucc_pred m) at 2.
now rewrite Zmul_succ_r, <- Zadd_sub_assoc, Zsub_diag, Zadd_0_r.
Qed.

Theorem Zmul_pred_l : forall n m : Z, (P n) * m == n * m - m.
Proof.
intros n m; rewrite (Zmul_comm (P n) m), (Zmul_comm n m). apply Zmul_pred_r.
Qed.

Theorem Zmul_opp_l : forall n m : Z, (- n) * m == - (n * m).
Proof.
intros n m. apply -> Zadd_move_0_r.
now rewrite <- Zmul_add_distr_r, Zadd_opp_diag_l, Zmul_0_l.
Qed.

Theorem Zmul_opp_r : forall n m : Z, n * (- m) == - (n * m).
Proof.
intros n m; rewrite (Zmul_comm n (- m)), (Zmul_comm n m); apply Zmul_opp_l.
Qed.

Theorem Zmul_opp_opp : forall n m : Z, (- n) * (- m) == n * m.
Proof.
intros n m; now rewrite Zmul_opp_l, Zmul_opp_r, Zopp_involutive.
Qed.

Theorem Zmul_sub_distr_l : forall n m p : Z, n * (m - p) == n * m - n * p.
Proof.
intros n m p. do 2 rewrite <- Zadd_opp_r. rewrite Zmul_add_distr_l.
now rewrite Zmul_opp_r.
Qed.

Theorem Zmul_sub_distr_r : forall n m p : Z, (n - m) * p == n * p - m * p.
Proof.
intros n m p; rewrite (Zmul_comm (n - m) p), (Zmul_comm n p), (Zmul_comm m p);
now apply Zmul_sub_distr_l.
Qed.

End ZMulPropFunct.


