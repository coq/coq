(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export ZAddOrder.

Module Type ZMulOrderPropFunct (Import Z : ZAxiomsSig').
Include ZAddOrderPropFunct Z.

Local Notation "- 1" := (-(1)).

Theorem mul_lt_mono_nonpos :
  forall n m p q, m <= 0 -> n < m -> q <= 0 -> p < q ->  m * q < n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply le_lt_trans with (m * p).
apply mul_le_mono_nonpos_l; [assumption | now apply lt_le_incl].
apply -> mul_lt_mono_neg_r; [assumption | now apply lt_le_trans with q].
Qed.

Theorem mul_le_mono_nonpos :
  forall n m p q, m <= 0 -> n <= m -> q <= 0 -> p <= q ->  m * q <= n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply le_trans with (m * p).
now apply mul_le_mono_nonpos_l.
apply mul_le_mono_nonpos_r; [now apply le_trans with q | assumption].
Qed.

Theorem mul_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (mul_0_l m). now apply mul_le_mono_nonpos_r.
Qed.

Theorem mul_nonneg_nonpos : forall n m, 0 <= n -> m <= 0 -> n * m <= 0.
Proof.
intros n m H1 H2.
rewrite <- (mul_0_l m). now apply mul_le_mono_nonpos_r.
Qed.

Theorem mul_nonpos_nonneg : forall n m, n <= 0 -> 0 <= m -> n * m <= 0.
Proof.
intros; rewrite mul_comm; now apply mul_nonneg_nonpos.
Qed.

Notation mul_pos := lt_0_mul (only parsing).

Theorem lt_mul_0 :
  forall n m, n * m < 0 <-> n < 0 /\ m > 0 \/ n > 0 /\ m < 0.
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite mul_0_l in H; false_hyp H lt_irrefl |];
(destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite mul_0_r in H; false_hyp H lt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m > 0) by now apply mul_neg_neg.
exfalso; now apply (lt_asymm (n * m) 0).
assert (H3 : n * m > 0) by now apply mul_pos_pos.
exfalso; now apply (lt_asymm (n * m) 0).
now apply mul_neg_pos. now apply mul_pos_neg.
Qed.

Notation mul_neg := lt_mul_0 (only parsing).

Theorem le_0_mul :
  forall n m, 0 <= n * m -> 0 <= n /\ 0 <= m \/ n <= 0 /\ m <= 0.
Proof.
assert (R : forall n, 0 == n <-> n == 0) by (intros; split; apply eq_sym).
intros n m. repeat rewrite lt_eq_cases. repeat rewrite R.
rewrite lt_0_mul, eq_mul_0.
pose proof (lt_trichotomy n 0); pose proof (lt_trichotomy m 0). tauto.
Qed.

Notation mul_nonneg := le_0_mul (only parsing).

Theorem le_mul_0 :
  forall n m, n * m <= 0 -> 0 <= n /\ m <= 0 \/ n <= 0 /\ 0 <= m.
Proof.
assert (R : forall n, 0 == n <-> n == 0) by (intros; split; apply eq_sym).
intros n m. repeat rewrite lt_eq_cases. repeat rewrite R.
rewrite lt_mul_0, eq_mul_0.
pose proof (lt_trichotomy n 0); pose proof (lt_trichotomy m 0). tauto.
Qed.

Notation mul_nonpos := le_mul_0 (only parsing).

Theorem le_0_square : forall n, 0 <= n * n.
Proof.
intro n; destruct (neg_nonneg_cases n).
apply lt_le_incl; now apply mul_neg_neg.
now apply mul_nonneg_nonneg.
Qed.

Notation square_nonneg := le_0_square (only parsing).

Theorem nlt_square_0 : forall n, ~ n * n < 0.
Proof.
intros n H. apply -> lt_nge in H. apply H. apply square_nonneg.
Qed.

Theorem square_lt_mono_nonpos : forall n m, n <= 0 -> m < n -> n * n < m * m.
Proof.
intros n m H1 H2. now apply mul_lt_mono_nonpos.
Qed.

Theorem square_le_mono_nonpos : forall n m, n <= 0 -> m <= n -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply mul_le_mono_nonpos.
Qed.

Theorem square_lt_simpl_nonpos : forall n m, m <= 0 -> n * n < m * m -> m < n.
Proof.
intros n m H1 H2. destruct (le_gt_cases n 0).
destruct (lt_ge_cases m n).
assumption. assert (F : m * m <= n * n) by now apply square_le_mono_nonpos.
apply -> le_ngt in F. false_hyp H2 F.
now apply le_lt_trans with 0.
Qed.

Theorem square_le_simpl_nonpos : forall n m, m <= 0 -> n * n <= m * m -> m <= n.
Proof.
intros n m H1 H2. destruct (le_gt_cases n 0).
destruct (le_gt_cases m n).
assumption. assert (F : m * m < n * n) by now apply square_lt_mono_nonpos.
apply -> lt_nge in F. false_hyp H2 F.
apply lt_le_incl; now apply le_lt_trans with 0.
Qed.

Theorem lt_1_mul_neg : forall n m, n < -1 -> m < 0 -> 1 < n * m.
Proof.
intros n m H1 H2. apply -> (mul_lt_mono_neg_r m) in H1.
apply <- opp_pos_neg in H2. rewrite mul_opp_l, mul_1_l in H1.
now apply lt_1_l with (- m).
assumption.
Qed.

Theorem lt_mul_n1_neg : forall n m, 1 < n -> m < 0 -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (mul_lt_mono_neg_r m) in H1.
rewrite mul_1_l in H1. now apply lt_n1_r with m.
assumption.
Qed.

Theorem lt_mul_n1_pos : forall n m, n < -1 -> 0 < m -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (mul_lt_mono_pos_r m) in H1.
rewrite mul_opp_l, mul_1_l in H1.
apply <- opp_neg_pos in H2. now apply lt_n1_r with (- m).
assumption.
Qed.

Theorem lt_1_mul_l : forall n m, 1 < n ->
 n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (lt_trichotomy m 0) as [H1 | [H1 | H1]].
left. now apply lt_mul_n1_neg.
right; left; now rewrite H1, mul_0_r.
right; right; now apply lt_1_mul_pos.
Qed.

Theorem lt_n1_mul_r : forall n m, n < -1 ->
 n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (lt_trichotomy m 0) as [H1 | [H1 | H1]].
right; right. now apply lt_1_mul_neg.
right; left; now rewrite H1, mul_0_r.
left. now apply lt_mul_n1_pos.
Qed.

Theorem eq_mul_1 : forall n m, n * m == 1 -> n == 1 \/ n == -1.
Proof.
assert (F : ~ 1 < -1).
intro H.
assert (H1 : -1 < 0). apply <- opp_neg_pos. apply lt_succ_diag_r.
assert (H2 : 1 < 0) by now apply lt_trans with (-1).
false_hyp H2 nlt_succ_diag_l.
zero_pos_neg n.
intros m H; rewrite mul_0_l in H; false_hyp H neq_succ_diag_r.
intros n H; split; apply <- le_succ_l in H; le_elim H.
intros m H1; apply (lt_1_mul_l n m) in H.
rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H F. false_hyp H neq_succ_diag_l. false_hyp H lt_irrefl.
intros; now left.
intros m H1; apply (lt_1_mul_l n m) in H. rewrite mul_opp_l in H1;
apply -> eq_opp_l in H1. rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H lt_irrefl. apply -> eq_opp_l in H. rewrite opp_0 in H.
false_hyp H neq_succ_diag_l. false_hyp H F.
intros; right; symmetry; now apply opp_wd.
Qed.

Theorem lt_mul_diag_l : forall n m, n < 0 -> (1 < m <-> n * m < n).
Proof.
intros n m H. stepr (n * m < n * 1) by now rewrite mul_1_r.
now apply mul_lt_mono_neg_l.
Qed.

Theorem lt_mul_diag_r : forall n m, 0 < n -> (1 < m <-> n < n * m).
Proof.
intros n m H. stepr (n * 1 < n * m) by now rewrite mul_1_r.
now apply mul_lt_mono_pos_l.
Qed.

Theorem le_mul_diag_l : forall n m, n < 0 -> (1 <= m <-> n * m <= n).
Proof.
intros n m H. stepr (n * m <= n * 1) by now rewrite mul_1_r.
now apply mul_le_mono_neg_l.
Qed.

Theorem le_mul_diag_r : forall n m, 0 < n -> (1 <= m <-> n <= n * m).
Proof.
intros n m H. stepr (n * 1 <= n * m) by now rewrite mul_1_r.
now apply mul_le_mono_pos_l.
Qed.

Theorem lt_mul_r : forall n m p, 0 < n -> 1 < p -> n < m -> n < m * p.
Proof.
intros. stepl (n * 1) by now rewrite mul_1_r.
apply mul_lt_mono_nonneg.
now apply lt_le_incl. assumption. apply le_0_1. assumption.
Qed.

End ZMulOrderPropFunct.

