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

Require Export ZPlus.

Module ZTimesPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZPlusPropMod := ZPlusPropFunct ZAxiomsMod.
Open Local Scope IntScope.

Theorem Ztimes_wd :
  forall n1 n2 : Z, n1 == n2 -> forall m1 m2 : Z, m1 == m2 -> n1 * m1 == n2 * m2.
Proof NZtimes_wd.

Theorem Ztimes_0_l : forall n : Z, 0 * n == 0.
Proof NZtimes_0_l.

Theorem Ztimes_succ_l : forall n m : Z, (S n) * m == n * m + m.
Proof NZtimes_succ_l.

(* Theorems that are valid for both natural numbers and integers *)

Theorem Ztimes_0_r : forall n : Z, n * 0 == 0.
Proof NZtimes_0_r.

Theorem Ztimes_succ_r : forall n m : Z, n * (S m) == n * m + n.
Proof NZtimes_succ_r.

Theorem Ztimes_comm : forall n m : Z, n * m == m * n.
Proof NZtimes_comm.

Theorem Ztimes_plus_distr_r : forall n m p : Z, (n + m) * p == n * p + m * p.
Proof NZtimes_plus_distr_r.

Theorem Ztimes_plus_distr_l : forall n m p : Z, n * (m + p) == n * m + n * p.
Proof NZtimes_plus_distr_l.

(* A note on naming: right (correspondingly, left) distributivity happens
when the sum is multiplied by a number on the right (left), not when the
sum itself is the right (left) factor in the product (see planetmath.org
and mathworld.wolfram.com). In the old library BinInt, distributivity over
subtraction was named correctly, but distributivity over addition was named
incorrectly. The names in Isabelle/HOL library are also incorrect. *)

Theorem Ztimes_assoc : forall n m p : Z, n * (m * p) == (n * m) * p.
Proof NZtimes_assoc.

Theorem Ztimes_1_l : forall n : Z, 1 * n == n.
Proof NZtimes_1_l.

Theorem Ztimes_1_r : forall n : Z, n * 1 == n.
Proof NZtimes_1_r.

(* The following two theorems are true in an ordered ring,
but since they don't mention order, we'll put them here *)

Theorem Zeq_times_0 : forall n m : Z, n * m == 0 <-> n == 0 \/ m == 0.
Proof NZeq_times_0.

Theorem Zneq_times_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZneq_times_0.

(* Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Ztimes_pred_r : forall n m : Z, n * (P m) == n * m - n.
Proof.
intros n m.
pattern m at 2; qsetoid_rewrite <- (Zsucc_pred m).
now rewrite Ztimes_succ_r, <- Zplus_minus_assoc, Zminus_diag, Zplus_0_r.
Qed.

Theorem Ztimes_pred_l : forall n m : Z, (P n) * m == n * m - m.
Proof.
intros n m; rewrite (Ztimes_comm (P n) m), (Ztimes_comm n m). apply Ztimes_pred_r.
Qed.

Theorem Ztimes_opp_l : forall n m : Z, (- n) * m == - (n * m).
Proof.
intros n m. apply -> Zplus_move_0_r.
now rewrite <- Ztimes_plus_distr_r, Zplus_opp_diag_l, Ztimes_0_l.
Qed.

Theorem Ztimes_opp_r : forall n m : Z, n * (- m) == - (n * m).
Proof.
intros n m; rewrite (Ztimes_comm n (- m)), (Ztimes_comm n m); apply Ztimes_opp_l.
Qed.

Theorem Ztimes_opp_opp : forall n m : Z, (- n) * (- m) == n * m.
Proof.
intros n m; now rewrite Ztimes_opp_l, Ztimes_opp_r, Zopp_involutive.
Qed.

Theorem Ztimes_minus_distr_l : forall n m p : Z, n * (m - p) == n * m - n * p.
Proof.
intros n m p. do 2 rewrite <- Zplus_opp_r. rewrite Ztimes_plus_distr_l.
now rewrite Ztimes_opp_r.
Qed.

Theorem Ztimes_minus_distr_r : forall n m p : Z, (n - m) * p == n * p - m * p.
Proof.
intros n m p; rewrite (Ztimes_comm (n - m) p), (Ztimes_comm n p), (Ztimes_comm m p);
now apply Ztimes_minus_distr_l.
Qed.

End ZTimesPropFunct.


