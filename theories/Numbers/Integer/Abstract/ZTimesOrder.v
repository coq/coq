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

Require Export ZPlusOrder.

Module ZTimesOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZPlusOrderPropMod := ZPlusOrderPropFunct ZAxiomsMod.
Open Local Scope IntScope.

Theorem Ztimes_lt_pred :
  forall p q n m : Z, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof NZtimes_lt_pred.

Theorem Ztimes_lt_mono_pos_l : forall p n m : Z, 0 < p -> (n < m <-> p * n < p * m).
Proof NZtimes_lt_mono_pos_l.

Theorem Ztimes_lt_mono_pos_r : forall p n m : Z, 0 < p -> (n < m <-> n * p < m * p).
Proof NZtimes_lt_mono_pos_r.

Theorem Ztimes_lt_mono_neg_l : forall p n m : Z, p < 0 -> (n < m <-> p * m < p * n).
Proof NZtimes_lt_mono_neg_l.

Theorem Ztimes_lt_mono_neg_r : forall p n m : Z, p < 0 -> (n < m <-> m * p < n * p).
Proof NZtimes_lt_mono_neg_r.

Theorem Ztimes_le_mono_nonneg_l : forall n m p : Z, 0 <= p -> n <= m -> p * n <= p * m.
Proof NZtimes_le_mono_nonneg_l.

Theorem Ztimes_le_mono_nonpos_l : forall n m p : Z, p <= 0 -> n <= m -> p * m <= p * n.
Proof NZtimes_le_mono_nonpos_l.

Theorem Ztimes_le_mono_nonneg_r : forall n m p : Z, 0 <= p -> n <= m -> n * p <= m * p.
Proof NZtimes_le_mono_nonneg_r.

Theorem Ztimes_le_mono_nonpos_r : forall n m p : Z, p <= 0 -> n <= m -> m * p <= n * p.
Proof NZtimes_le_mono_nonpos_r.

Theorem Ztimes_cancel_l : forall n m p : Z, p ~= 0 -> (p * n == p * m <-> n == m).
Proof NZtimes_cancel_l.

Theorem Ztimes_cancel_r : forall n m p : Z, p ~= 0 -> (n * p == m * p <-> n == m).
Proof NZtimes_cancel_r.

Theorem Ztimes_id_l : forall n m : Z, m ~= 0 -> (n * m == m <-> n == 1).
Proof NZtimes_id_l.

Theorem Ztimes_id_r : forall n m : Z, n ~= 0 -> (n * m == n <-> m == 1).
Proof NZtimes_id_r.

Theorem Ztimes_le_mono_pos_l : forall n m p : Z, 0 < p -> (n <= m <-> p * n <= p * m).
Proof NZtimes_le_mono_pos_l.

Theorem Ztimes_le_mono_pos_r : forall n m p : Z, 0 < p -> (n <= m <-> n * p <= m * p).
Proof NZtimes_le_mono_pos_r.

Theorem Ztimes_le_mono_neg_l : forall n m p : Z, p < 0 -> (n <= m <-> p * m <= p * n).
Proof NZtimes_le_mono_neg_l.

Theorem Ztimes_le_mono_neg_r : forall n m p : Z, p < 0 -> (n <= m <-> m * p <= n * p).
Proof NZtimes_le_mono_neg_r.

Theorem Ztimes_lt_mono_nonneg :
  forall n m p q : Z, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof NZtimes_lt_mono_nonneg.

Theorem Ztimes_lt_mono_nonpos :
  forall n m p q : Z, m <= 0 -> n < m -> q <= 0 -> p < q ->  m * q < n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply Zle_lt_trans with (m * p).
apply Ztimes_le_mono_nonpos_l; [assumption | now apply Zlt_le_incl].
apply -> Ztimes_lt_mono_neg_r; [assumption | now apply Zlt_le_trans with q].
Qed.

Theorem Ztimes_le_mono_nonneg :
  forall n m p q : Z, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof NZtimes_le_mono_nonneg.

Theorem Ztimes_le_mono_nonpos :
  forall n m p q : Z, m <= 0 -> n <= m -> q <= 0 -> p <= q ->  m * q <= n * p.
Proof.
intros n m p q H1 H2 H3 H4.
apply Zle_trans with (m * p).
now apply Ztimes_le_mono_nonpos_l.
apply Ztimes_le_mono_nonpos_r; [now apply Zle_trans with q | assumption].
Qed.

Theorem Ztimes_pos_pos : forall n m : Z, 0 < n -> 0 < m -> 0 < n * m.
Proof NZtimes_pos_pos.

Theorem Ztimes_neg_neg : forall n m : Z, n < 0 -> m < 0 -> 0 < n * m.
Proof NZtimes_neg_neg.

Theorem Ztimes_pos_neg : forall n m : Z, 0 < n -> m < 0 -> n * m < 0.
Proof NZtimes_pos_neg.

Theorem Ztimes_neg_pos : forall n m : Z, n < 0 -> 0 < m -> n * m < 0.
Proof NZtimes_neg_pos.

Theorem Ztimes_nonneg_nonneg : forall n m : Z, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (Ztimes_0_l m). now apply Ztimes_le_mono_nonneg_r.
Qed.

Theorem Ztimes_nonpos_nonpos : forall n m : Z, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (Ztimes_0_l m). now apply Ztimes_le_mono_nonpos_r.
Qed.

Theorem Ztimes_nonneg_nonpos : forall n m : Z, 0 <= n -> m <= 0 -> n * m <= 0.
Proof.
intros n m H1 H2.
rewrite <- (Ztimes_0_l m). now apply Ztimes_le_mono_nonpos_r.
Qed.

Theorem Ztimes_nonpos_nonneg : forall n m : Z, n <= 0 -> 0 <= m -> n * m <= 0.
Proof.
intros; rewrite Ztimes_comm; now apply Ztimes_nonneg_nonpos.
Qed.

Theorem Zlt_1_times_pos : forall n m : Z, 1 < n -> 0 < m -> 1 < n * m.
Proof NZlt_1_times_pos.

Theorem Zeq_times_0 : forall n m : Z, n * m == 0 <-> n == 0 \/ m == 0.
Proof NZeq_times_0.

Theorem Zneq_times_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZneq_times_0.

Theorem Zeq_square_0 : forall n : Z, n * n == 0 <-> n == 0.
Proof NZeq_square_0.

Theorem Zeq_times_0_l : forall n m : Z, n * m == 0 -> m ~= 0 -> n == 0.
Proof NZeq_times_0_l.

Theorem Zeq_times_0_r : forall n m : Z, n * m == 0 -> n ~= 0 -> m == 0.
Proof NZeq_times_0_r.

Theorem Zlt_0_times : forall n m : Z, 0 < n * m <-> 0 < n /\ 0 < m \/ m < 0 /\ n < 0.
Proof NZlt_0_times.

Notation Ztimes_pos := Zlt_0_times (only parsing).

Theorem Zlt_times_0 :
  forall n m : Z, n * m < 0 <-> n < 0 /\ m > 0 \/ n > 0 /\ m < 0.
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (Zlt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite Ztimes_0_l in H; false_hyp H Zlt_irrefl |];
(destruct (Zlt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite Ztimes_0_r in H; false_hyp H Zlt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m > 0) by now apply Ztimes_neg_neg.
elimtype False; now apply (Zlt_asymm (n * m) 0).
assert (H3 : n * m > 0) by now apply Ztimes_pos_pos.
elimtype False; now apply (Zlt_asymm (n * m) 0).
now apply Ztimes_neg_pos. now apply Ztimes_pos_neg.
Qed.

Notation Ztimes_neg := Zlt_times_0 (only parsing).

Theorem Zle_0_times :
  forall n m : Z, 0 <= n * m -> 0 <= n /\ 0 <= m \/ n <= 0 /\ m <= 0.
Proof.
assert (R : forall n : Z, 0 == n <-> n == 0) by (intros; split; apply Zeq_symm).
intros n m. repeat rewrite Zlt_eq_cases. repeat rewrite R.
rewrite Zlt_0_times, Zeq_times_0.
pose proof (Zlt_trichotomy n 0); pose proof (Zlt_trichotomy m 0). tauto.
Qed.

Notation Ztimes_nonneg := Zle_0_times (only parsing).

Theorem Zle_times_0 :
  forall n m : Z, n * m <= 0 -> 0 <= n /\ m <= 0 \/ n <= 0 /\ 0 <= m.
Proof.
assert (R : forall n : Z, 0 == n <-> n == 0) by (intros; split; apply Zeq_symm).
intros n m. repeat rewrite Zlt_eq_cases. repeat rewrite R.
rewrite Zlt_times_0, Zeq_times_0.
pose proof (Zlt_trichotomy n 0); pose proof (Zlt_trichotomy m 0). tauto.
Qed.

Notation Ztimes_nonpos := Zle_times_0 (only parsing).

Theorem Zle_0_square : forall n : Z, 0 <= n * n.
Proof.
intro n; destruct (Zneg_nonneg_cases n).
apply Zlt_le_incl; now apply Ztimes_neg_neg.
now apply Ztimes_nonneg_nonneg.
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
intros n m H1 H2. now apply Ztimes_lt_mono_nonpos.
Qed.

Theorem Zsquare_le_mono_nonneg : forall n m : Z, 0 <= n -> n <= m -> n * n <= m * m.
Proof NZsquare_le_mono_nonneg.

Theorem Zsquare_le_mono_nonpos : forall n m : Z, n <= 0 -> m <= n -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply Ztimes_le_mono_nonpos.
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

Theorem Ztimes_2_mono_l : forall n m : Z, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof NZtimes_2_mono_l.

Theorem Zlt_1_times_neg : forall n m : Z, n < -1 -> m < 0 -> 1 < n * m.
Proof.
intros n m H1 H2. apply -> (NZtimes_lt_mono_neg_r m) in H1.
apply <- Zopp_pos_neg in H2. rewrite Ztimes_opp_l, Ztimes_1_l in H1.
now apply Zlt_1_l with (- m).
assumption.
Qed.

Theorem Zlt_times_n1_neg : forall n m : Z, 1 < n -> m < 0 -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (NZtimes_lt_mono_neg_r m) in H1.
rewrite Ztimes_1_l in H1. now apply Zlt_n1_r with m.
assumption.
Qed.

Theorem Zlt_times_n1_pos : forall n m : Z, n < -1 -> 0 < m -> n * m < -1.
Proof.
intros n m H1 H2. apply -> (NZtimes_lt_mono_pos_r m) in H1.
rewrite Ztimes_opp_l, Ztimes_1_l in H1.
apply <- Zopp_neg_pos in H2. now apply Zlt_n1_r with (- m).
assumption.
Qed.

Theorem Zlt_1_times_l : forall n m : Z, 1 < n -> n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (Zlt_trichotomy m 0) as [H1 | [H1 | H1]].
left. now apply Zlt_times_n1_neg.
right; left; now rewrite H1, Ztimes_0_r.
right; right; now apply Zlt_1_times_pos.
Qed.

Theorem Zlt_n1_times_r : forall n m : Z, n < -1 -> n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof.
intros n m H; destruct (Zlt_trichotomy m 0) as [H1 | [H1 | H1]].
right; right. now apply Zlt_1_times_neg.
right; left; now rewrite H1, Ztimes_0_r.
left. now apply Zlt_times_n1_pos.
Qed.

Theorem Zeq_times_1 : forall n m : Z, n * m == 1 -> n == 1 \/ n == -1.
Proof.
assert (F : ~ 1 < -1).
intro H.
assert (H1 : -1 < 0). apply <- Zopp_neg_pos. apply Zlt_succ_diag_r.
assert (H2 : 1 < 0) by now apply Zlt_trans with (-1). false_hyp H2 Znlt_succ_diag_l.
Z0_pos_neg n.
intros m H; rewrite Ztimes_0_l in H; false_hyp H Zneq_succ_diag_r.
intros n H; split; apply <- Zle_succ_l in H; le_elim H.
intros m H1; apply (Zlt_1_times_l n m) in H.
rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H F. false_hyp H Zneq_succ_diag_l. false_hyp H Zlt_irrefl.
intros; now left.
intros m H1; apply (Zlt_1_times_l n m) in H. rewrite Ztimes_opp_l in H1;
apply -> Zeq_opp_l in H1. rewrite H1 in H; destruct H as [H | [H | H]].
false_hyp H Zlt_irrefl. apply -> Zeq_opp_l in H. rewrite Zopp_0 in H.
false_hyp H Zneq_succ_diag_l. false_hyp H F.
intros; right; symmetry; now apply Zopp_wd.
Qed.

Theorem Zlt_times_diag_l : forall n m : Z, n < 0 -> (1 < m <-> n * m < n).
Proof.
intros n m H. stepr (n * m < n * 1) by now rewrite Ztimes_1_r.
now apply Ztimes_lt_mono_neg_l.
Qed.

Theorem Zlt_times_diag_r : forall n m : Z, 0 < n -> (1 < m <-> n < n * m).
Proof.
intros n m H. stepr (n * 1 < n * m) by now rewrite Ztimes_1_r.
now apply Ztimes_lt_mono_pos_l.
Qed.

Theorem Zle_times_diag_l : forall n m : Z, n < 0 -> (1 <= m <-> n * m <= n).
Proof.
intros n m H. stepr (n * m <= n * 1) by now rewrite Ztimes_1_r.
now apply Ztimes_le_mono_neg_l.
Qed.

Theorem Zle_times_diag_r : forall n m : Z, 0 < n -> (1 <= m <-> n <= n * m).
Proof.
intros n m H. stepr (n * 1 <= n * m) by now rewrite Ztimes_1_r.
now apply Ztimes_le_mono_pos_l.
Qed.

Theorem Zlt_times_r : forall n m p : Z, 0 < n -> 1 < p -> n < m -> n < m * p.
Proof.
intros. stepl (n * 1) by now rewrite Ztimes_1_r.
apply Ztimes_lt_mono_nonneg.
now apply Zlt_le_incl. assumption. apply Zle_0_1. assumption.
Qed.

End ZTimesOrderPropFunct.

