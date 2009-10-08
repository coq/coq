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

Require Export ZAddOrder.

Module ZMulOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZAddOrderPropMod := ZAddOrderPropFunct ZAxiomsMod.
Open Local Scope IntScope.

Theorem Zmul_lt_pred :
  forall p q n m : Z, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof NZmul_lt_pred.

Theorem Zmul_lt_mono_pos_l : forall p n m : Z, 0 < p -> (n < m <-> p * n < p * m).
Proof NZmul_lt_mono_pos_l.

Theorem Zmul_lt_mono_pos_r : forall p n m : Z, 0 < p -> (n < m <-> n * p < m * p).
Proof NZmul_lt_mono_pos_r.

Theorem Zmul_lt_mono_neg_l : forall p n m : Z, p < 0 -> (n < m <-> p * m < p * n).
Proof NZmul_lt_mono_neg_l.

Theorem Zmul_lt_mono_neg_r : forall p n m : Z, p < 0 -> (n < m <-> m * p < n * p).
Proof NZmul_lt_mono_neg_r.

Theorem Zmul_le_mono_nonneg_l : forall n m p : Z, 0 <= p -> n <= m -> p * n <= p * m.
Proof NZmul_le_mono_nonneg_l.

Theorem Zmul_le_mono_nonpos_l : forall n m p : Z, p <= 0 -> n <= m -> p * m <= p * n.
Proof NZmul_le_mono_nonpos_l.

Theorem Zmul_le_mono_nonneg_r : forall n m p : Z, 0 <= p -> n <= m -> n * p <= m * p.
Proof NZmul_le_mono_nonneg_r.

Theorem Zmul_le_mono_nonpos_r : forall n m p : Z, p <= 0 -> n <= m -> m * p <= n * p.
Proof NZmul_le_mono_nonpos_r.

Theorem Zmul_cancel_l : forall n m p : Z, p ~= 0 -> (p * n == p * m <-> n == m).
Proof NZmul_cancel_l.

Theorem Zmul_cancel_r : forall n m p : Z, p ~= 0 -> (n * p == m * p <-> n == m).
Proof NZmul_cancel_r.

Theorem Zmul_id_l : forall n m : Z, m ~= 0 -> (n * m == m <-> n == 1).
Proof NZmul_id_l.

Theorem Zmul_id_r : forall n m : Z, n ~= 0 -> (n * m == n <-> m == 1).
Proof NZmul_id_r.

Theorem Zmul_le_mono_pos_l : forall n m p : Z, 0 < p -> (n <= m <-> p * n <= p * m).
Proof NZmul_le_mono_pos_l.

Theorem Zmul_le_mono_pos_r : forall n m p : Z, 0 < p -> (n <= m <-> n * p <= m * p).
Proof NZmul_le_mono_pos_r.

Theorem Zmul_le_mono_neg_l : forall n m p : Z, p < 0 -> (n <= m <-> p * m <= p * n).
Proof NZmul_le_mono_neg_l.

Theorem Zmul_le_mono_neg_r : forall n m p : Z, p < 0 -> (n <= m <-> m * p <= n * p).
Proof NZmul_le_mono_neg_r.

Theorem Zmul_lt_mono_nonneg :
  forall n m p q : Z, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof NZmul_lt_mono_nonneg.

Theorem Zmul_lt_mono_nonpos :
  forall n m p q : Z, m <= 0 -> n < m -> q <= 0 -> p < q ->  m * q < n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply Zle_lt_trans with (m * p).
apply Zmul_le_mono_nonpos_l; [assumption | now apply Zlt_le_incl].
apply -> Zmul_lt_mono_neg_r; [assumption | now apply Zlt_le_trans with q].
Qed.

Theorem Zmul_le_mono_nonneg :
  forall n m p q : Z, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof NZmul_le_mono_nonneg.

Theorem Zmul_le_mono_nonpos :
  forall n m p q : Z, m <= 0 -> n <= m -> q <= 0 -> p <= q ->  m * q <= n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply Zle_trans with (m * p).
now apply Zmul_le_mono_nonpos_l.
apply Zmul_le_mono_nonpos_r; [now apply Zle_trans with q | assumption].
Qed.

Theorem Zmul_pos_pos : forall n m : Z, 0 < n -> 0 < m -> 0 < n * m.
Proof NZmul_pos_pos.

Theorem Zmul_neg_neg : forall n m : Z, n < 0 -> m < 0 -> 0 < n * m.
Proof NZmul_neg_neg.

Theorem Zmul_pos_neg : forall n m : Z, 0 < n -> m < 0 -> n * m < 0.
Proof NZmul_pos_neg.

Theorem Zmul_neg_pos : forall n m : Z, n < 0 -> 0 < m -> n * m < 0.
Proof NZmul_neg_pos.

Theorem Zmul_nonneg_nonneg : forall n m : Z, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (Zmul_0_l m). now apply Zmul_le_mono_nonneg_r.
Qed.

Theorem Zmul_nonpos_nonpos : forall n m : Z, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (Zmul_0_l m). now apply Zmul_le_mono_nonpos_r.
Qed.

Theorem Zmul_nonneg_nonpos : forall n m : Z, 0 <= n -> m <= 0 -> n * m <= 0.
Proof.
intros n m H1 H2.
rewrite <- (Zmul_0_l m). now apply Zmul_le_mono_nonpos_r.
Qed.

Theorem Zmul_nonpos_nonneg : forall n m : Z, n <= 0 -> 0 <= m -> n * m <= 0.
Proof.
intros; rewrite Zmul_comm; now apply Zmul_nonneg_nonpos.
Qed.

Theorem Zlt_1_mul_pos : forall n m : Z, 1 < n -> 0 < m -> 1 < n * m.
Proof NZlt_1_mul_pos.

Theorem Zeq_mul_0 : forall n m : Z, n * m == 0 <-> n == 0 \/ m == 0.
Proof NZeq_mul_0.

Theorem Zneq_mul_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZneq_mul_0.

Theorem Zeq_square_0 : forall n : Z, n * n == 0 <-> n == 0.
Proof NZeq_square_0.

Theorem Zeq_mul_0_l : forall n m : Z, n * m == 0 -> m ~= 0 -> n == 0.
Proof NZeq_mul_0_l.

Theorem Zeq_mul_0_r : forall n m : Z, n * m == 0 -> n ~= 0 -> m == 0.
Proof NZeq_mul_0_r.

Theorem Zlt_0_mul : forall n m : Z, 0 < n * m <-> 0 < n /\ 0 < m \/ m < 0 /\ n < 0.
Proof NZlt_0_mul.

Notation Zmul_pos := Zlt_0_mul (only parsing).

Theorem Zlt_mul_0 :
  forall n m : Z, n * m < 0 <-> n < 0 /\ m > 0 \/ n > 0 /\ m < 0.
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (Zlt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite Zmul_0_l in H; false_hyp H Zlt_irrefl |];
(destruct (Zlt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite Zmul_0_r in H; false_hyp H Zlt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m > 0) by now apply Zmul_neg_neg.
exfalso; now apply (Zlt_asymm (n * m) 0).
assert (H3 : n * m > 0) by now apply Zmul_pos_pos.
exfalso; now apply (Zlt_asymm (n * m) 0).
now apply Zmul_neg_pos. now apply Zmul_pos_neg.
Qed.

Notation Zmul_neg := Zlt_mul_0 (only parsing).

Theorem Zle_0_mul :
  forall n m : Z, 0 <= n * m -> 0 <= n /\ 0 <= m \/ n <= 0 /\ m <= 0.
Proof.
assert (R : forall n : Z, 0 == n <-> n == 0) by (intros; split; apply Zeq_sym).
intros n m. repeat rewrite Zlt_eq_cases. repeat rewrite R.
rewrite Zlt_0_mul, Zeq_mul_0.
pose proof (Zlt_trichotomy n 0); pose proof (Zlt_trichotomy m 0). tauto.
Qed.

Notation Zmul_nonneg := Zle_0_mul (only parsing).

Theorem Zle_mul_0 :
  forall n m : Z, n * m <= 0 -> 0 <= n /\ m <= 0 \/ n <= 0 /\ 0 <= m.
Proof.
assert (R : forall n : Z, 0 == n <-> n == 0) by (intros; split; apply Zeq_sym).
intros n m. repeat rewrite Zlt_eq_cases. repeat rewrite R.
rewrite Zlt_mul_0, Zeq_mul_0.
pose proof (Zlt_trichotomy n 0); pose proof (Zlt_trichotomy m 0). tauto.
Qed.

Notation Zmul_nonpos := Zle_mul_0 (only parsing).

Theorem Zle_0_square : forall n : Z, 0 <= n * n.
Proof.
intro n; destruct (Zneg_nonneg_cases n).
apply Zlt_le_incl; now apply Zmul_neg_neg.
now apply Zmul_nonneg_nonneg.
Qed.

Notation Zsquare_nonneg := Zle_0_square (only parsing).

Theorem Znlt_square_0 : forall n : Z, ~ n * n < 0.
Proof.
intros n H. apply -> Zlt_nge in H. apply H. apply Zsquare_nonneg.
Qed.

Theorem Zsquare_lt_mono_nonneg : forall n m : Z, 0 <= n -> n < m -> n * n < m * m.
Proof NZsquare_lt_mono_nonneg.

Theorem Zsquare_lt_mono_nonpos : forall n m : Z, n <= 0 -> m < n -> n * n < m * m.
Proof.
intros n m H1 H2. now apply Zmul_lt_mono_nonpos.
Qed.

Theorem Zsquare_le_mono_nonneg : forall n m : Z, 0 <= n -> n <= m -> n * n <= m * m.
Proof NZsquare_le_mono_nonneg.

Theorem Zsquare_le_mono_nonpos : forall n m : Z, n <= 0 -> m <= n -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply Zmul_le_mono_nonpos.
Qed.

Theorem Zsquare_lt_simpl_nonneg : forall n m : Z, 0 <= m -> n * n < m * m -> n < m.
Proof NZsquare_lt_simpl_nonneg.

Theorem Zsquare_le_simpl_nonneg : forall n m : Z, 0 <= m -> n * n <= m * m -> n <= m.
Proof NZsquare_le_simpl_nonneg.

Theorem Zsquare_lt_simpl_nonpos : forall n m : Z, m <= 0 -> n * n < m * m -> m < n.
Proof.
intros n m H1 H2. destruct (Zle_gt_cases n 0).
destruct (NZlt_ge_cases m n).
assumption. assert (F : m * m <= n * n) by now apply Zsquare_le_mono_nonpos.
apply -> NZle_ngt in F. false_hyp H2 F.
now apply Zle_lt_trans with 0.
Qed.

Theorem Zsquare_le_simpl_nonpos : forall n m : NZ, m <= 0 -> n * n <= m * m -> m <= n.
Proof.
intros n m H1 H2. destruct (NZle_gt_cases n 0).
destruct (NZle_gt_cases m n).
assumption. assert (F : m * m < n * n) by now apply Zsquare_lt_mono_nonpos.
apply -> NZlt_nge in F. false_hyp H2 F.
apply Zlt_le_incl; now apply NZle_lt_trans with 0.
Qed.

Theorem Zmul_2_mono_l : forall n m : Z, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof NZmul_2_mono_l.

Theorem Zlt_1_mul_neg : forall n m : Z, n < -1 -> m < 0 -> 1 < n * m.
Proof.
intros n m H1 H2. apply -> (NZmul_lt_mono_neg_r m) in H1.
apply <- Zopp_pos_neg in H2. rewrite Zmul_opp_l, Zmul_1_l in H1.
now apply Zlt_1_l with (- m).
assumption.
Qed.

Theorem Zlt_mul_n1_neg : forall n m : Z, 1 < n -> m < 0 -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (NZmul_lt_mono_neg_r m) in H1.
rewrite Zmul_1_l in H1. now apply Zlt_n1_r with m.
assumption.
Qed.

Theorem Zlt_mul_n1_pos : forall n m : Z, n < -1 -> 0 < m -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (NZmul_lt_mono_pos_r m) in H1.
rewrite Zmul_opp_l, Zmul_1_l in H1.
apply <- Zopp_neg_pos in H2. now apply Zlt_n1_r with (- m).
assumption.
Qed.

Theorem Zlt_1_mul_l : forall n m : Z, 1 < n -> n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (Zlt_trichotomy m 0) as [H1 | [H1 | H1]].
left. now apply Zlt_mul_n1_neg.
right; left; now rewrite H1, Zmul_0_r.
right; right; now apply Zlt_1_mul_pos.
Qed.

Theorem Zlt_n1_mul_r : forall n m : Z, n < -1 -> n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (Zlt_trichotomy m 0) as [H1 | [H1 | H1]].
right; right. now apply Zlt_1_mul_neg.
right; left; now rewrite H1, Zmul_0_r.
left. now apply Zlt_mul_n1_pos.
Qed.

Theorem Zeq_mul_1 : forall n m : Z, n * m == 1 -> n == 1 \/ n == -1.
Proof.
assert (F : ~ 1 < -1).
intro H.
assert (H1 : -1 < 0). apply <- Zopp_neg_pos. apply Zlt_succ_diag_r.
assert (H2 : 1 < 0) by now apply Zlt_trans with (-1). false_hyp H2 Znlt_succ_diag_l.
Z0_pos_neg n.
intros m H; rewrite Zmul_0_l in H; false_hyp H Zneq_succ_diag_r.
intros n H; split; apply <- Zle_succ_l in H; le_elim H.
intros m H1; apply (Zlt_1_mul_l n m) in H.
rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H F. false_hyp H Zneq_succ_diag_l. false_hyp H Zlt_irrefl.
intros; now left.
intros m H1; apply (Zlt_1_mul_l n m) in H. rewrite Zmul_opp_l in H1;
apply -> Zeq_opp_l in H1. rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H Zlt_irrefl. apply -> Zeq_opp_l in H. rewrite Zopp_0 in H.
false_hyp H Zneq_succ_diag_l. false_hyp H F.
intros; right; symmetry; now apply Zopp_wd.
Qed.

Theorem Zlt_mul_diag_l : forall n m : Z, n < 0 -> (1 < m <-> n * m < n).
Proof.
intros n m H. stepr (n * m < n * 1) by now rewrite Zmul_1_r.
now apply Zmul_lt_mono_neg_l.
Qed.

Theorem Zlt_mul_diag_r : forall n m : Z, 0 < n -> (1 < m <-> n < n * m).
Proof.
intros n m H. stepr (n * 1 < n * m) by now rewrite Zmul_1_r.
now apply Zmul_lt_mono_pos_l.
Qed.

Theorem Zle_mul_diag_l : forall n m : Z, n < 0 -> (1 <= m <-> n * m <= n).
Proof.
intros n m H. stepr (n * m <= n * 1) by now rewrite Zmul_1_r.
now apply Zmul_le_mono_neg_l.
Qed.

Theorem Zle_mul_diag_r : forall n m : Z, 0 < n -> (1 <= m <-> n <= n * m).
Proof.
intros n m H. stepr (n * 1 <= n * m) by now rewrite Zmul_1_r.
now apply Zmul_le_mono_pos_l.
Qed.

Theorem Zlt_mul_r : forall n m p : Z, 0 < n -> 1 < p -> n < m -> n < m * p.
Proof.
intros. stepl (n * 1) by now rewrite Zmul_1_r.
apply Zmul_lt_mono_nonneg.
now apply Zlt_le_incl. assumption. apply Zle_0_1. assumption.
Qed.

End ZMulOrderPropFunct.

