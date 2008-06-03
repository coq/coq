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

Require Export NMulOrder.

Module NSubPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NMulOrderPropMod := NMulOrderPropFunct NAxiomsMod.
Open Local Scope NatScope.

Theorem sub_wd :
  forall n1 n2 : N, n1 == n2 -> forall m1 m2 : N, m1 == m2 -> n1 - m1 == n2 - m2.
Proof NZsub_wd.

Theorem sub_0_r : forall n : N, n - 0 == n.
Proof NZsub_0_r.

Theorem sub_succ_r : forall n m : N, n - (S m) == P (n - m).
Proof NZsub_succ_r.

Theorem sub_1_r : forall n : N, n - 1 == P n.
Proof.
intro n; rewrite sub_succ_r; now rewrite sub_0_r.
Qed.

Theorem sub_0_l : forall n : N, 0 - n == 0.
Proof.
induct n.
apply sub_0_r.
intros n IH; rewrite sub_succ_r; rewrite IH. now apply pred_0.
Qed.

Theorem sub_succ : forall n m : N, S n - S m == n - m.
Proof.
intro n; induct m.
rewrite sub_succ_r. do 2 rewrite sub_0_r. now rewrite pred_succ.
intros m IH. rewrite sub_succ_r. rewrite IH. now rewrite sub_succ_r.
Qed.

Theorem sub_diag : forall n : N, n - n == 0.
Proof.
induct n. apply sub_0_r. intros n IH; rewrite sub_succ; now rewrite IH.
Qed.

Theorem sub_gt : forall n m : N, n > m -> n - m ~= 0.
Proof.
intros n m H; elim H using lt_ind_rel; clear n m H.
solve_relation_wd.
intro; rewrite sub_0_r; apply neq_succ_0.
intros; now rewrite sub_succ.
Qed.

Theorem add_sub_assoc : forall n m p : N, p <= m -> n + (m - p) == (n + m) - p.
Proof.
intros n m p; induct p.
intro; now do 2 rewrite sub_0_r.
intros p IH H. do 2 rewrite sub_succ_r.
rewrite <- IH by (apply lt_le_incl; now apply -> le_succ_l).
rewrite add_pred_r by (apply sub_gt; now apply -> le_succ_l).
reflexivity.
Qed.

Theorem sub_succ_l : forall n m : N, n <= m -> S m - n == S (m - n).
Proof.
intros n m H. rewrite <- (add_1_l m). rewrite <- (add_1_l (m - n)).
symmetry; now apply add_sub_assoc.
Qed.

Theorem add_sub : forall n m : N, (n + m) - m == n.
Proof.
intros n m. rewrite <- add_sub_assoc by (apply le_refl).
rewrite sub_diag; now rewrite add_0_r.
Qed.

Theorem sub_add : forall n m : N, n <= m -> (m - n) + n == m.
Proof.
intros n m H. rewrite add_comm. rewrite add_sub_assoc by assumption.
rewrite add_comm. apply add_sub.
Qed.

Theorem add_sub_eq_l : forall n m p : N, m + p == n -> n - m == p.
Proof.
intros n m p H. symmetry.
assert (H1 : m + p - m == n - m) by now rewrite H.
rewrite add_comm in H1. now rewrite add_sub in H1.
Qed.

Theorem add_sub_eq_r : forall n m p : N, m + p == n -> n - p == m.
Proof.
intros n m p H; rewrite add_comm in H; now apply add_sub_eq_l.
Qed.

(* This could be proved by adding m to both sides. Then the proof would
use add_sub_assoc and sub_0_le, which is proven below. *)

Theorem add_sub_eq_nz : forall n m p : N, p ~= 0 -> n - m == p -> m + p == n.
Proof.
intros n m p H; double_induct n m.
intros m H1; rewrite sub_0_l in H1. symmetry in H1; false_hyp H1 H.
intro n; rewrite sub_0_r; now rewrite add_0_l.
intros n m IH H1. rewrite sub_succ in H1. apply IH in H1.
rewrite add_succ_l; now rewrite H1.
Qed.

Theorem sub_add_distr : forall n m p : N, n - (m + p) == (n - m) - p.
Proof.
intros n m; induct p.
rewrite add_0_r; now rewrite sub_0_r.
intros p IH. rewrite add_succ_r; do 2 rewrite sub_succ_r. now rewrite IH.
Qed.

Theorem add_sub_swap : forall n m p : N, p <= n -> n + m - p == n - p + m.
Proof.
intros n m p H.
rewrite (add_comm n m).
rewrite <- add_sub_assoc by assumption.
now rewrite (add_comm m (n - p)).
Qed.

(** Sub and order *)

Theorem le_sub_l : forall n m : N, n - m <= n.
Proof.
intro n; induct m.
rewrite sub_0_r; now apply eq_le_incl.
intros m IH. rewrite sub_succ_r.
apply le_trans with (n - m); [apply le_pred_l | assumption].
Qed.

Theorem sub_0_le : forall n m : N, n - m == 0 <-> n <= m.
Proof.
double_induct n m.
intro m; split; intro; [apply le_0_l | apply sub_0_l].
intro m; rewrite sub_0_r; split; intro H;
[false_hyp H neq_succ_0 | false_hyp H nle_succ_0].
intros n m H. rewrite <- succ_le_mono. now rewrite sub_succ.
Qed.

(** Sub and mul *)

Theorem mul_pred_r : forall n m : N, n * (P m) == n * m - n.
Proof.
intros n m; cases m.
now rewrite pred_0, mul_0_r, sub_0_l.
intro m; rewrite pred_succ, mul_succ_r, <- add_sub_assoc.
now rewrite sub_diag, add_0_r.
now apply eq_le_incl.
Qed.

Theorem mul_sub_distr_r : forall n m p : N, (n - m) * p == n * p - m * p.
Proof.
intros n m p; induct n.
now rewrite sub_0_l, mul_0_l, sub_0_l.
intros n IH. destruct (le_gt_cases m n) as [H | H].
rewrite sub_succ_l by assumption. do 2 rewrite mul_succ_l.
rewrite (add_comm ((n - m) * p) p), (add_comm (n * p) p).
rewrite <- (add_sub_assoc p (n * p) (m * p)) by now apply mul_le_mono_r.
now apply <- add_cancel_l.
assert (H1 : S n <= m); [now apply <- le_succ_l |].
setoid_replace (S n - m) with 0 by now apply <- sub_0_le.
setoid_replace ((S n * p) - m * p) with 0 by (apply <- sub_0_le; now apply mul_le_mono_r).
apply mul_0_l.
Qed.

Theorem mul_sub_distr_l : forall n m p : N, p * (n - m) == p * n - p * m.
Proof.
intros n m p; rewrite (mul_comm p (n - m)), (mul_comm p n), (mul_comm p m).
apply mul_sub_distr_r.
Qed.

End NSubPropFunct.

