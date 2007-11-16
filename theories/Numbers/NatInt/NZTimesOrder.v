(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Import NZAxioms.
Require Import NZPlusOrder.

Module NZTimesOrderPropFunct (Import NZOrdAxiomsMod : NZOrdAxiomsSig).
Module Export NZPlusOrderPropMod := NZPlusOrderPropFunct NZOrdAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZtimes_lt_pred :
  forall p q n m : NZ, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof.
intros p q n m H. rewrite <- H. do 2 rewrite NZtimes_succ_l.
rewrite <- (NZplus_assoc (p * n) n m).
rewrite <- (NZplus_assoc (p * m) m n).
rewrite (NZplus_comm n m). now rewrite <- NZplus_lt_mono_r.
Qed.

Theorem NZtimes_lt_mono_pos_l : forall p n m : NZ, 0 < p -> (n < m <-> p * n < p * m).
Proof.
NZord_induct p.
intros n m H; false_hyp H NZlt_irrefl.
intros p H IH n m H1. do 2 rewrite NZtimes_succ_l.
le_elim H. assert (LR : forall n m : NZ, n < m -> p * n + n < p * m + m).
intros n1 m1 H2. apply NZplus_lt_mono; [now apply -> IH | assumption].
split; [apply LR |]. intro H2. apply -> NZlt_dne; intro H3.
apply <- NZle_ngt in H3. le_elim H3.
apply NZlt_asymm in H2. apply H2. now apply LR.
rewrite H3 in H2; false_hyp H2 NZlt_irrefl.
rewrite <- H; do 2 rewrite NZtimes_0_l; now do 2 rewrite NZplus_0_l.
intros p H1 _ n m H2. apply NZlt_asymm in H1. false_hyp H2 H1.
Qed.

Theorem NZtimes_lt_mono_pos_r : forall p n m : NZ, 0 < p -> (n < m <-> n * p < m * p).
Proof.
intros p n m.
rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p). now apply NZtimes_lt_mono_pos_l.
Qed.

Theorem NZtimes_lt_mono_neg_l : forall p n m : NZ, p < 0 -> (n < m <-> p * m < p * n).
Proof.
NZord_induct p.
intros n m H; false_hyp H NZlt_irrefl.
intros p H1 _ n m H2. apply NZlt_succ_l in H2. apply <- NZnle_gt in H2. false_hyp H1 H2.
intros p H IH n m H1. apply <- NZle_succ_l in H.
le_elim H. assert (LR : forall n m : NZ, n < m -> p * m < p * n).
intros n1 m1 H2. apply (NZle_lt_plus_lt n1 m1).
now apply NZlt_le_incl. do 2 rewrite <- NZtimes_succ_l. now apply -> IH.
split; [apply LR |]. intro H2. apply -> NZlt_dne; intro H3.
apply <- NZle_ngt in H3. le_elim H3.
apply NZlt_asymm in H2. apply H2. now apply LR.
rewrite H3 in H2; false_hyp H2 NZlt_irrefl.
rewrite (NZtimes_lt_pred p (S p)); [reflexivity |].
rewrite H; do 2 rewrite NZtimes_0_l; now do 2 rewrite NZplus_0_l.
Qed.

Theorem NZtimes_lt_mono_neg_r : forall p n m : NZ, p < 0 -> (n < m <-> m * p < n * p).
Proof.
intros p n m.
rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p). now apply NZtimes_lt_mono_neg_l.
Qed.

Theorem NZtimes_le_mono_nonneg_l : forall n m p : NZ, 0 <= p -> n <= m -> p * n <= p * m.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply NZlt_le_incl. now apply -> NZtimes_lt_mono_pos_l.
apply NZeq_le_incl; now rewrite H2.
apply NZeq_le_incl; rewrite <- H1; now do 2 rewrite NZtimes_0_l.
Qed.

Theorem NZtimes_le_mono_nonpos_l : forall n m p : NZ, p <= 0 -> n <= m -> p * m <= p * n.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. apply NZlt_le_incl. now apply -> NZtimes_lt_mono_neg_l.
apply NZeq_le_incl; now rewrite H2.
apply NZeq_le_incl; rewrite H1; now do 2 rewrite NZtimes_0_l.
Qed.

Theorem NZtimes_le_mono_nonneg_r : forall n m p : NZ, 0 <= p -> n <= m -> n * p <= m * p.
Proof.
intros n m p H1 H2; rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p);
now apply NZtimes_le_mono_nonneg_l.
Qed.

Theorem NZtimes_le_mono_nonpos_r : forall n m p : NZ, p <= 0 -> n <= m -> m * p <= n * p.
Proof.
intros n m p H1 H2; rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p);
now apply NZtimes_le_mono_nonpos_l.
Qed.

Theorem NZtimes_cancel_l : forall n m p : NZ, p ~= 0 -> (p * n == p * m <-> n == m).
Proof.
intros n m p H; split; intro H1.
destruct (NZlt_trichotomy p 0) as [H2 | [H2 | H2]].
apply -> NZeq_dne; intro H3. apply -> NZlt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * m < p * n); [now apply -> NZtimes_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
assert (H4 : p * n < p * m); [now apply -> NZtimes_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
false_hyp H2 H.
apply -> NZeq_dne; intro H3. apply -> NZlt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * n < p * m); [now apply -> NZtimes_lt_mono_pos_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
assert (H4 : p * m < p * n); [now apply -> NZtimes_lt_mono_pos_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
now rewrite H1.
Qed.

Theorem NZtimes_cancel_r : forall n m p : NZ, p ~= 0 -> (n * p == m * p <-> n == m).
Proof.
intros n m p. rewrite (NZtimes_comm n p), (NZtimes_comm m p); apply NZtimes_cancel_l.
Qed.

Theorem NZtimes_le_mono_pos_l : forall n m p : NZ, 0 < p -> (n <= m <-> p * n <= p * m).
Proof.
intros n m p H; do 2 rewrite NZlt_eq_cases.
rewrite (NZtimes_lt_mono_pos_l p n m); [assumption |].
now rewrite -> (NZtimes_cancel_l n m p);
[intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl |].
Qed.

Theorem NZtimes_le_mono_pos_r : forall n m p : NZ, 0 < p -> (n <= m <-> n * p <= m * p).
Proof.
intros n m p. rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p);
apply NZtimes_le_mono_pos_l.
Qed.

Theorem NZtimes_le_mono_neg_l : forall n m p : NZ, p < 0 -> (n <= m <-> p * m <= p * n).
Proof.
intros n m p H; do 2 rewrite NZlt_eq_cases.
rewrite (NZtimes_lt_mono_neg_l p n m); [assumption |].
rewrite -> (NZtimes_cancel_l m n p);
[intro H1; rewrite H1 in H; false_hyp H NZlt_irrefl |].
now setoid_replace (n == m) with (m == n) using relation iff by (split; now intro).
Qed.

Theorem NZtimes_le_mono_neg_r : forall n m p : NZ, p < 0 -> (n <= m <-> m * p <= n * p).
Proof.
intros n m p. rewrite (NZtimes_comm n p); rewrite (NZtimes_comm m p);
apply NZtimes_le_mono_neg_l.
Qed.

Theorem NZtimes_lt_mono_nonneg :
  forall n m p q : NZ, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof.
intros n m p q H1 H2 H3 H4.
apply NZle_lt_trans with (m * p).
apply NZtimes_le_mono_nonneg_r; [assumption | now apply NZlt_le_incl].
apply -> NZtimes_lt_mono_pos_l; [assumption | now apply NZle_lt_trans with n].
Qed.

(* There are still many variants of the theorem above. One can assume 0 < n
or 0 < p or n <= m or p <= q. *)

Theorem NZtimes_le_mono_nonneg :
  forall n m p q : NZ, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof.
intros n m p q H1 H2 H3 H4.
le_elim H2; le_elim H4.
apply NZlt_le_incl; now apply NZtimes_lt_mono_nonneg.
rewrite <- H4; apply NZtimes_le_mono_nonneg_r; [assumption | now apply NZlt_le_incl].
rewrite <- H2; apply NZtimes_le_mono_nonneg_l; [assumption | now apply NZlt_le_incl].
rewrite H2; rewrite H4; now apply NZeq_le_incl.
Qed.

Theorem NZtimes_pos_pos : forall n m : NZ, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_pos_r.
Qed.

Theorem NZtimes_neg_neg : forall n m : NZ, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_neg_r.
Qed.

Theorem NZtimes_pos_neg : forall n m : NZ, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_neg_r.
Qed.

Theorem NZtimes_neg_pos : forall n m : NZ, n < 0 -> 0 < m -> n * m < 0.
Proof.
intros; rewrite NZtimes_comm; now apply NZtimes_pos_neg.
Qed.

Theorem NZlt_1_times_pos : forall n m : NZ, 1 < n -> 0 < m -> 1 < n * m.
Proof.
intros n m H1 H2. apply -> (NZtimes_lt_mono_pos_r m) in H1.
rewrite NZtimes_1_l in H1. now apply NZlt_1_l with m.
assumption.
Qed.

Theorem NZeq_times_0 : forall n m : NZ, n * m == 0 <-> n == 0 \/ m == 0.
Proof.
intros n m; split.
intro H; destruct (NZlt_trichotomy n 0) as [H1 | [H1 | H1]];
destruct (NZlt_trichotomy m 0) as [H2 | [H2 | H2]];
try (now right); try (now left).
elimtype False; now apply (NZlt_neq 0 (n * m)); [apply NZtimes_neg_neg |].
elimtype False; now apply (NZlt_neq (n * m) 0); [apply NZtimes_neg_pos |].
elimtype False; now apply (NZlt_neq (n * m) 0); [apply NZtimes_pos_neg |].
elimtype False; now apply (NZlt_neq 0 (n * m)); [apply NZtimes_pos_pos |].
intros [H | H]. now rewrite H, NZtimes_0_l. now rewrite H, NZtimes_0_r.
Qed.

Theorem NZneq_times_0 : forall n m : NZ, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof.
intros n m; split; intro H.
intro H1; apply -> NZeq_times_0 in H1. tauto.
split; intro H1; rewrite H1 in H;
(rewrite NZtimes_0_l in H || rewrite NZtimes_0_r in H); now apply H.
Qed.

Theorem NZeq_times_0_l : forall n m : NZ, n * m == 0 -> m ~= 0 -> n == 0.
Proof.
intros n m H1 H2. apply -> NZeq_times_0 in H1. destruct H1 as [H1 | H1].
assumption. false_hyp H1 H2.
Qed.

Theorem NZeq_times_0_r : forall n m : NZ, n * m == 0 -> n ~= 0 -> m == 0.
Proof.
intros n m H1 H2; apply -> NZeq_times_0 in H1. destruct H1 as [H1 | H1].
false_hyp H1 H2. assumption.
Qed.

Theorem NZlt_0_times : forall n m : NZ, 0 < n * m <-> (0 < n /\ 0 < m) \/ (m < 0 /\ n < 0).
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (NZlt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite NZtimes_0_l in H; false_hyp H NZlt_irrefl |];
(destruct (NZlt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite NZtimes_0_r in H; false_hyp H NZlt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m < 0) by now apply NZtimes_neg_pos.
elimtype False; now apply (NZlt_asymm (n * m) 0).
assert (H3 : n * m < 0) by now apply NZtimes_pos_neg.
elimtype False; now apply (NZlt_asymm (n * m) 0).
now apply NZtimes_pos_pos. now apply NZtimes_neg_neg.
Qed.

Theorem NZsquare_lt_mono_nonneg : forall n m : NZ, 0 <= n -> n < m -> n * n < m * m.
Proof.
intros n m H1 H2. now apply NZtimes_lt_mono_nonneg.
Qed.

Theorem NZsquare_le_mono_nonneg : forall n m : NZ, 0 <= n -> n <= m -> n * n <= m * m.
Proof.
intros n m H1 H2. now apply NZtimes_le_mono_nonneg.
Qed.

(* The converse theorems require nonnegativity (or nonpositivity) of the
other variable *)

Theorem NZsquare_lt_simpl_nonneg : forall n m : NZ, 0 <= m -> n * n < m * m -> n < m.
Proof.
intros n m H1 H2. destruct (NZlt_ge_cases n 0).
now apply NZlt_le_trans with 0.
destruct (NZlt_ge_cases n m).
assumption. assert (F : m * m <= n * n) by now apply NZsquare_le_mono_nonneg.
apply -> NZle_ngt in F. false_hyp H2 F.
Qed.

Theorem NZsquare_le_simpl_nonneg : forall n m : NZ, 0 <= m -> n * n <= m * m -> n <= m.
Proof.
intros n m H1 H2. destruct (NZlt_ge_cases n 0).
apply NZlt_le_incl; now apply NZlt_le_trans with 0.
destruct (NZle_gt_cases n m).
assumption. assert (F : m * m < n * n) by now apply NZsquare_lt_mono_nonneg.
apply -> NZlt_nge in F. false_hyp H2 F.
Qed.

Theorem NZtimes_2_mono_l : forall n m : NZ, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof.
intros n m H. apply <- NZle_succ_l in H.
apply -> (NZtimes_le_mono_pos_l (S n) m (1 + 1)) in H.
repeat rewrite NZtimes_plus_distr_r in *; repeat rewrite NZtimes_1_l in *.
repeat rewrite NZplus_succ_r in *. repeat rewrite NZplus_succ_l in *. rewrite NZplus_0_l.
now apply -> NZle_succ_l.
apply NZplus_pos_pos; now apply NZlt_succ_diag_r.
Qed.

End NZTimesOrderPropFunct.
