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

Require Import NZAxioms.
Require Import NZOrder.

Module NZAddOrderPropFunct (Import NZOrdAxiomsMod : NZOrdAxiomsSig).
Module Export NZOrderPropMod := NZOrderPropFunct NZOrdAxiomsMod.
Open Local Scope NatIntScope.

Theorem NZadd_lt_mono_l : forall n m p : NZ, n < m <-> p + n < p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZadd_0_l.
intro p. do 2 rewrite NZadd_succ_l. now rewrite <- NZsucc_lt_mono.
Qed.

Theorem NZadd_lt_mono_r : forall n m p : NZ, n < m <-> n + p < m + p.
Proof.
intros n m p.
rewrite (NZadd_comm n p); rewrite (NZadd_comm m p); apply NZadd_lt_mono_l.
Qed.

Theorem NZadd_lt_mono : forall n m p q : NZ, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_trans with (m + p);
[now apply -> NZadd_lt_mono_r | now apply -> NZadd_lt_mono_l].
Qed.

Theorem NZadd_le_mono_l : forall n m p : NZ, n <= m <-> p + n <= p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZadd_0_l.
intro p. do 2 rewrite NZadd_succ_l. now rewrite <- NZsucc_le_mono.
Qed.

Theorem NZadd_le_mono_r : forall n m p : NZ, n <= m <-> n + p <= m + p.
Proof.
intros n m p.
rewrite (NZadd_comm n p); rewrite (NZadd_comm m p); apply NZadd_le_mono_l.
Qed.

Theorem NZadd_le_mono : forall n m p q : NZ, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply NZle_trans with (m + p);
[now apply -> NZadd_le_mono_r | now apply -> NZadd_le_mono_l].
Qed.

Theorem NZadd_lt_le_mono : forall n m p q : NZ, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_le_trans with (m + p);
[now apply -> NZadd_lt_mono_r | now apply -> NZadd_le_mono_l].
Qed.

Theorem NZadd_le_lt_mono : forall n m p q : NZ, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZle_lt_trans with (m + p);
[now apply -> NZadd_le_mono_r | now apply -> NZadd_lt_mono_l].
Qed.

Theorem NZadd_pos_pos : forall n m : NZ, 0 < n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (NZadd_0_l 0). now apply NZadd_lt_mono.
Qed.

Theorem NZadd_pos_nonneg : forall n m : NZ, 0 < n -> 0 <= m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (NZadd_0_l 0). now apply NZadd_lt_le_mono.
Qed.

Theorem NZadd_nonneg_pos : forall n m : NZ, 0 <= n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (NZadd_0_l 0). now apply NZadd_le_lt_mono.
Qed.

Theorem NZadd_nonneg_nonneg : forall n m : NZ, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
intros n m H1 H2. rewrite <- (NZadd_0_l 0). now apply NZadd_le_mono.
Qed.

Theorem NZlt_add_pos_l : forall n m : NZ, 0 < n -> m < n + m.
Proof.
intros n m H. apply -> (NZadd_lt_mono_r 0 n m) in H.
now rewrite NZadd_0_l in H.
Qed.

Theorem NZlt_add_pos_r : forall n m : NZ, 0 < n -> m < m + n.
Proof.
intros; rewrite NZadd_comm; now apply NZlt_add_pos_l.
Qed.

Theorem NZle_lt_add_lt : forall n m p q : NZ, n <= m -> p + m < q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases q p); [| assumption].
pose proof (NZadd_le_mono q p n m H H1) as H3. apply <- NZnle_gt in H2.
false_hyp H3 H2.
Qed.

Theorem NZlt_le_add_lt : forall n m p q : NZ, n < m -> p + m <= q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases q p); [| assumption].
pose proof (NZadd_le_lt_mono q p n m H H1) as H3. apply <- NZnle_gt in H3.
false_hyp H2 H3.
Qed.

Theorem NZle_le_add_le : forall n m p q : NZ, n <= m -> p + m <= q + n -> p <= q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases p q); [assumption |].
pose proof (NZadd_lt_le_mono q p n m H H1) as H3. apply <- NZnle_gt in H3.
false_hyp H2 H3.
Qed.

Theorem NZadd_lt_cases : forall n m p q : NZ, n + m < p + q -> n < p \/ m < q.
Proof.
intros n m p q H;
destruct (NZle_gt_cases p n) as [H1 | H1].
destruct (NZle_gt_cases q m) as [H2 | H2].
pose proof (NZadd_le_mono p n q m H1 H2) as H3. apply -> NZle_ngt in H3.
false_hyp H H3.
now right. now left.
Qed.

Theorem NZadd_le_cases : forall n m p q : NZ, n + m <= p + q -> n <= p \/ m <= q.
Proof.
intros n m p q H.
destruct (NZle_gt_cases n p) as [H1 | H1]. now left.
destruct (NZle_gt_cases m q) as [H2 | H2]. now right.
assert (H3 : p + q < n + m) by now apply NZadd_lt_mono.
apply -> NZle_ngt in H. false_hyp H3 H.
Qed.

Theorem NZadd_neg_cases : forall n m : NZ, n + m < 0 -> n < 0 \/ m < 0.
Proof.
intros n m H; apply NZadd_lt_cases; now rewrite NZadd_0_l.
Qed.

Theorem NZadd_pos_cases : forall n m : NZ, 0 < n + m -> 0 < n \/ 0 < m.
Proof.
intros n m H; apply NZadd_lt_cases; now rewrite NZadd_0_l.
Qed.

Theorem NZadd_nonpos_cases : forall n m : NZ, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof.
intros n m H; apply NZadd_le_cases; now rewrite NZadd_0_l.
Qed.

Theorem NZadd_nonneg_cases : forall n m : NZ, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof.
intros n m H; apply NZadd_le_cases; now rewrite NZadd_0_l.
Qed.

End NZAddOrderPropFunct.

