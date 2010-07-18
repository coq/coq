(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NZAxioms.
Require Import NZAddOrder.
Import Morphisms_Prop. (* For Hints *)

Module Type NZMulOrderPropSig (Import NZ : NZOrdAxiomsSig').
Include NZAddOrderPropSig NZ.

Theorem mul_lt_pred :
  forall p q n m, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof.
intros p q n m H. rewrite <- H. nzsimpl.
rewrite <- ! add_assoc, (add_comm n m).
now rewrite <- add_lt_mono_r.
Qed.

Theorem mul_lt_mono_pos_l : forall p n m, 0 < p -> (n < m <-> p * n < p * m).
Proof.
nzord_induct p.
intros n m H; false_hyp H lt_irrefl.
intros p H IH n m H1. nzsimpl.
le_elim H. assert (LR : forall n m, n < m -> p * n + n < p * m + m).
intros n1 m1 H2. apply add_lt_mono; [now apply -> IH | assumption].
split; [apply LR |]. intro H2. apply -> lt_dne; intro H3.
apply <- le_ngt in H3. le_elim H3.
apply lt_asymm in H2. apply H2. now apply LR.
rewrite H3 in H2; false_hyp H2 lt_irrefl.
rewrite <- H; now nzsimpl.
intros p H1 _ n m H2. destruct (lt_asymm _ _ H1 H2).
Qed.

Theorem mul_lt_mono_pos_r : forall p n m, 0 < p -> (n < m <-> n * p < m * p).
Proof.
intros p n m.
rewrite (mul_comm n p), (mul_comm m p). now apply mul_lt_mono_pos_l.
Qed.

Theorem mul_lt_mono_neg_l : forall p n m, p < 0 -> (n < m <-> p * m < p * n).
Proof.
nzord_induct p.
intros n m H; false_hyp H lt_irrefl.
intros p H1 _ n m H2. apply lt_succ_l in H2. apply <- nle_gt in H2.
false_hyp H1 H2.
intros p H IH n m H1. apply <- le_succ_l in H.
le_elim H. assert (LR : forall n m, n < m -> p * m < p * n).
intros n1 m1 H2. apply (le_lt_add_lt n1 m1).
now apply lt_le_incl. rewrite <- 2 mul_succ_l. now apply -> IH.
split; [apply LR |]. intro H2. apply -> lt_dne; intro H3.
apply <- le_ngt in H3. le_elim H3.
apply lt_asymm in H2. apply H2. now apply LR.
rewrite H3 in H2; false_hyp H2 lt_irrefl.
rewrite (mul_lt_pred p (S p)) by reflexivity.
rewrite H; do 2 rewrite mul_0_l; now do 2 rewrite add_0_l.
Qed.

Theorem mul_lt_mono_neg_r : forall p n m, p < 0 -> (n < m <-> m * p < n * p).
Proof.
intros p n m.
rewrite (mul_comm n p), (mul_comm m p). now apply mul_lt_mono_neg_l.
Qed.

Theorem mul_le_mono_nonneg_l : forall n m p, 0 <= p -> n <= m -> p * n <= p * m.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply lt_le_incl. now apply -> mul_lt_mono_pos_l.
apply eq_le_incl; now rewrite H2.
apply eq_le_incl; rewrite <- H1; now do 2 rewrite mul_0_l.
Qed.

Theorem mul_le_mono_nonpos_l : forall n m p, p <= 0 -> n <= m -> p * m <= p * n.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply lt_le_incl. now apply -> mul_lt_mono_neg_l.
apply eq_le_incl; now rewrite H2.
apply eq_le_incl; rewrite H1; now do 2 rewrite mul_0_l.
Qed.

Theorem mul_le_mono_nonneg_r : forall n m p, 0 <= p -> n <= m -> n * p <= m * p.
Proof.
intros n m p H1 H2;
rewrite (mul_comm n p), (mul_comm m p); now apply mul_le_mono_nonneg_l.
Qed.

Theorem mul_le_mono_nonpos_r : forall n m p, p <= 0 -> n <= m -> m * p <= n * p.
Proof.
intros n m p H1 H2;
rewrite (mul_comm n p), (mul_comm m p); now apply mul_le_mono_nonpos_l.
Qed.

Theorem mul_cancel_l : forall n m p, p ~= 0 -> (p * n == p * m <-> n == m).
Proof.
intros n m p H; split; intro H1.
destruct (lt_trichotomy p 0) as [H2 | [H2 | H2]].
apply -> eq_dne; intro H3. apply -> lt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * m < p * n); [now apply -> mul_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 lt_irrefl.
assert (H4 : p * n < p * m); [now apply -> mul_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 lt_irrefl.
false_hyp H2 H.
apply -> eq_dne; intro H3. apply -> lt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * n < p * m) by (now apply -> mul_lt_mono_pos_l).
rewrite H1 in H4; false_hyp H4 lt_irrefl.
assert (H4 : p * m < p * n) by (now apply -> mul_lt_mono_pos_l).
rewrite H1 in H4; false_hyp H4 lt_irrefl.
now rewrite H1.
Qed.

Theorem mul_cancel_r : forall n m p, p ~= 0 -> (n * p == m * p <-> n == m).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_cancel_l.
Qed.

Theorem mul_id_l : forall n m, m ~= 0 -> (n * m == m <-> n == 1).
Proof.
intros n m H.
stepl (n * m == 1 * m) by now rewrite mul_1_l. now apply mul_cancel_r.
Qed.

Theorem mul_id_r : forall n m, n ~= 0 -> (n * m == n <-> m == 1).
Proof.
intros n m; rewrite mul_comm; apply mul_id_l.
Qed.

Theorem mul_le_mono_pos_l : forall n m p, 0 < p -> (n <= m <-> p * n <= p * m).
Proof.
intros n m p H; do 2 rewrite lt_eq_cases.
rewrite (mul_lt_mono_pos_l p n m) by assumption.
now rewrite -> (mul_cancel_l n m p) by
(intro H1; rewrite H1 in H; false_hyp H lt_irrefl).
Qed.

Theorem mul_le_mono_pos_r : forall n m p, 0 < p -> (n <= m <-> n * p <= m * p).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_le_mono_pos_l.
Qed.

Theorem mul_le_mono_neg_l : forall n m p, p < 0 -> (n <= m <-> p * m <= p * n).
Proof.
intros n m p H; do 2 rewrite lt_eq_cases.
rewrite (mul_lt_mono_neg_l p n m); [| assumption].
rewrite -> (mul_cancel_l m n p)
 by (intro H1; rewrite H1 in H; false_hyp H lt_irrefl).
now setoid_replace (n == m) with (m == n) by (split; now intro).
Qed.

Theorem mul_le_mono_neg_r : forall n m p, p < 0 -> (n <= m <-> m * p <= n * p).
Proof.
intros n m p. rewrite (mul_comm n p), (mul_comm m p); apply mul_le_mono_neg_l.
Qed.

Theorem mul_lt_mono_nonneg :
  forall n m p q, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof.
intros n m p q H1 H2 H3 H4.
apply le_lt_trans with (m * p).
apply mul_le_mono_nonneg_r; [assumption | now apply lt_le_incl].
apply -> mul_lt_mono_pos_l; [assumption | now apply le_lt_trans with n].
Qed.

(* There are still many variants of the theorem above. One can assume 0 < n
or 0 < p or n <= m or p <= q. *)

Theorem mul_le_mono_nonneg :
  forall n m p q, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof.
intros n m p q H1 H2 H3 H4.
le_elim H2; le_elim H4.
apply lt_le_incl; now apply mul_lt_mono_nonneg.
rewrite <- H4; apply mul_le_mono_nonneg_r; [assumption | now apply lt_le_incl].
rewrite <- H2; apply mul_le_mono_nonneg_l; [assumption | now apply lt_le_incl].
rewrite H2; rewrite H4; now apply eq_le_incl.
Qed.

Theorem mul_pos_pos : forall n m, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply -> mul_lt_mono_pos_r.
Qed.

Theorem mul_neg_neg : forall n m, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply -> mul_lt_mono_neg_r.
Qed.

Theorem mul_pos_neg : forall n m, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m H1 H2. rewrite <- (mul_0_l m). now apply -> mul_lt_mono_neg_r.
Qed.

Theorem mul_neg_pos : forall n m, n < 0 -> 0 < m -> n * m < 0.
Proof.
intros; rewrite mul_comm; now apply mul_pos_neg.
Qed.

Theorem mul_nonneg_nonneg : forall n m, 0 <= n -> 0 <= m -> 0 <= n*m.
Proof.
intros. rewrite <- (mul_0_l m). apply mul_le_mono_nonneg; order.
Qed.

Theorem lt_1_mul_pos : forall n m, 1 < n -> 0 < m -> 1 < n * m.
Proof.
intros n m H1 H2. apply -> (mul_lt_mono_pos_r m) in H1.
rewrite mul_1_l in H1. now apply lt_1_l with m.
assumption.
Qed.

Theorem eq_mul_0 : forall n m, n * m == 0 <-> n == 0 \/ m == 0.
Proof.
intros n m; split.
intro H; destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
try (now right); try (now left).
exfalso; now apply (lt_neq 0 (n * m)); [apply mul_neg_neg |].
exfalso; now apply (lt_neq (n * m) 0); [apply mul_neg_pos |].
exfalso; now apply (lt_neq (n * m) 0); [apply mul_pos_neg |].
exfalso; now apply (lt_neq 0 (n * m)); [apply mul_pos_pos |].
intros [H | H]. now rewrite H, mul_0_l. now rewrite H, mul_0_r.
Qed.

Theorem neq_mul_0 : forall n m, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof.
intros n m; split; intro H.
intro H1; apply -> eq_mul_0 in H1. tauto.
split; intro H1; rewrite H1 in H;
(rewrite mul_0_l in H || rewrite mul_0_r in H); now apply H.
Qed.

Theorem eq_square_0 : forall n, n * n == 0 <-> n == 0.
Proof.
intro n; rewrite eq_mul_0; tauto.
Qed.

Theorem eq_mul_0_l : forall n m, n * m == 0 -> m ~= 0 -> n == 0.
Proof.
intros n m H1 H2. apply -> eq_mul_0 in H1. destruct H1 as [H1 | H1].
assumption. false_hyp H1 H2.
Qed.

Theorem eq_mul_0_r : forall n m, n * m == 0 -> n ~= 0 -> m == 0.
Proof.
intros n m H1 H2; apply -> eq_mul_0 in H1. destruct H1 as [H1 | H1].
false_hyp H1 H2. assumption.
Qed.

Theorem lt_0_mul : forall n m, 0 < n * m <-> (0 < n /\ 0 < m) \/ (m < 0 /\ n < 0).
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite mul_0_l in H; false_hyp H lt_irrefl |];
(destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite mul_0_r in H; false_hyp H lt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m < 0) by now apply mul_neg_pos.
exfalso; now apply (lt_asymm (n * m) 0).
assert (H3 : n * m < 0) by now apply mul_pos_neg.
exfalso; now apply (lt_asymm (n * m) 0).
now apply mul_pos_pos. now apply mul_neg_neg.
Qed.

Theorem square_lt_mono_nonneg : forall n m, 0 <= n -> n < m -> n * n < m * m.
Proof.
intros n m H1 H2. now apply mul_lt_mono_nonneg.
Qed.

Theorem square_le_mono_nonneg : forall n m, 0 <= n -> n <= m -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply mul_le_mono_nonneg.
Qed.

(* The converse theorems require nonnegativity (or nonpositivity) of the
other variable *)

Theorem square_lt_simpl_nonneg : forall n m, 0 <= m -> n * n < m * m -> n < m.
Proof.
intros n m H1 H2. destruct (lt_ge_cases n 0).
now apply lt_le_trans with 0.
destruct (lt_ge_cases n m).
assumption. assert (F : m * m <= n * n) by now apply square_le_mono_nonneg.
apply -> le_ngt in F. false_hyp H2 F.
Qed.

Theorem square_le_simpl_nonneg : forall n m, 0 <= m -> n * n <= m * m -> n <= m.
Proof.
intros n m H1 H2. destruct (lt_ge_cases n 0).
apply lt_le_incl; now apply lt_le_trans with 0.
destruct (le_gt_cases n m).
assumption. assert (F : m * m < n * n) by now apply square_lt_mono_nonneg.
apply -> lt_nge in F. false_hyp H2 F.
Qed.

Theorem mul_2_mono_l : forall n m, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof.
intros n m. rewrite <- le_succ_l, (mul_le_mono_pos_l (S n) m (1 + 1)).
rewrite !mul_add_distr_r; nzsimpl; now rewrite le_succ_l.
apply add_pos_pos; now apply lt_0_1.
Qed.

End NZMulOrderPropSig.
