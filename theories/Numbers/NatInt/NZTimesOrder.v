Require Import NZAxioms.
Require Import NZOrder.

Module NZTimesOrderPropFunct (Import NZOrdAxiomsMod : NZOrdAxiomsSig).
Module Export NZOrderPropMod := NZOrderPropFunct NZOrdAxiomsMod.
Open Local Scope NatIntScope.

(** Addition and order *)

Theorem NZplus_lt_mono_l : forall n m p : NZ, n < m <-> p + n < p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZplus_0_l.
intro p. do 2 rewrite NZplus_succ_l. now rewrite <- NZsucc_lt_mono.
Qed.

Theorem NZplus_lt_mono_r : forall n m p : NZ, n < m <-> n + p < m + p.
Proof.
intros n m p.
rewrite (NZplus_comm n p); rewrite (NZplus_comm m p); apply NZplus_lt_mono_l.
Qed.

Theorem NZplus_lt_mono : forall n m p q : NZ, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_trans with (m + p);
[now apply -> NZplus_lt_mono_r | now apply -> NZplus_lt_mono_l].
Qed.

Theorem NZplus_le_mono_l : forall n m p : NZ, n <= m <-> p + n <= p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZplus_0_l.
intro p. do 2 rewrite NZplus_succ_l. now rewrite <- NZsucc_le_mono.
Qed.

Theorem NZplus_le_mono_r : forall n m p : NZ, n <= m <-> n + p <= m + p.
Proof.
intros n m p.
rewrite (NZplus_comm n p); rewrite (NZplus_comm m p); apply NZplus_le_mono_l.
Qed.

Theorem NZplus_le_mono : forall n m p q : NZ, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply NZle_trans with (m + p);
[now apply -> NZplus_le_mono_r | now apply -> NZplus_le_mono_l].
Qed.

Theorem NZplus_lt_le_mono : forall n m p q : NZ, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_le_trans with (m + p);
[now apply -> NZplus_lt_mono_r | now apply -> NZplus_le_mono_l].
Qed.

Theorem NZplus_le_lt_mono : forall n m p q : NZ, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZle_lt_trans with (m + p);
[now apply -> NZplus_le_mono_r | now apply -> NZplus_lt_mono_l].
Qed.

Theorem NZle_lt_plus_lt : forall n m p q : NZ, n <= m -> p + m < q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases q p); [| assumption].
pose proof (NZplus_le_mono q p n m H H1) as H3. apply <- NZnle_gt in H2.
false_hyp H3 H2.
Qed.

Theorem NZlt_le_plus_lt : forall n m p q : NZ, n < m -> p + m <= q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases q p); [| assumption].
pose proof (NZplus_le_lt_mono q p n m H H1) as H3. apply <- NZnle_gt in H3.
false_hyp H2 H3.
Qed.

Theorem NZle_le_plus_lt : forall n m p q : NZ, n <= m -> p + m <= q + n -> p <= q.
Proof.
intros n m p q H1 H2. destruct (NZle_gt_cases p q); [assumption |].
pose proof (NZplus_lt_le_mono q p n m H H1) as H3. apply <- NZnle_gt in H3.
false_hyp H2 H3.
Qed.

Theorem NZplus_lt_cases : forall n m p q : NZ, n + m < p + q -> n < p \/ m < q.
Proof.
intros n m p q H;
destruct (NZle_gt_cases p n) as [H1 | H1].
destruct (NZle_gt_cases q m) as [H2 | H2].
pose proof (NZplus_le_mono p n q m H1 H2) as H3. apply -> NZle_ngt in H3.
false_hyp H H3.
now right. now left.
Qed.

Theorem NZplus_le_cases : forall n m p q : NZ, n + m <= p + q -> n <= p \/ m <= q.
Proof.
intros n m p q H.
destruct (NZle_gt_cases n p) as [H1 | H1]. now left.
destruct (NZle_gt_cases m q) as [H2 | H2]. now right.
assert (H3 : p + q < n + m) by now apply NZplus_lt_mono.
apply -> NZle_ngt in H. false_hyp H3 H.
Qed.

Theorem NZplus_neg_cases : forall n m : NZ, n + m < 0 -> n < 0 \/ m < 0.
Proof.
intros n m H; apply NZplus_lt_cases; now rewrite NZplus_0_l.
Qed.

Theorem NZplus_pos_cases : forall n m : NZ, 0 < n + m -> 0 < n \/ 0 < m.
Proof.
intros n m H; apply NZplus_lt_cases; now rewrite NZplus_0_l.
Qed.

Theorem NZplus_nonpos_cases : forall n m : NZ, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof.
intros n m H; apply NZplus_le_cases; now rewrite NZplus_0_l.
Qed.

Theorem NZplus_nonneg_cases : forall n m : NZ, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof.
intros n m H; apply NZplus_le_cases; now rewrite NZplus_0_l.
Qed.

(** Multiplication and order *)

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
intros p H1 _ n m H2. apply NZlt_succ_lt in H2. apply <- NZnle_gt in H2. false_hyp H1 H2.
intros p H IH n m H1. apply -> NZlt_le_succ in H.
le_elim H. assert (LR : forall n m : NZ, n < m -> p * m < p * n).
intros n1 m1 H2. apply (NZle_lt_plus_lt n1 m1).
now le_less. do 2 rewrite <- NZtimes_succ_l. now apply -> IH.
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
le_elim H2. le_less. now apply -> NZtimes_lt_mono_pos_l.
le_equal; now rewrite H2.
le_equal; rewrite <- H1; now do 2 rewrite NZtimes_0_l.
Qed.

Theorem NZtimes_le_mono_nonpos_l : forall n m p : NZ, p <= 0 -> n <= m -> p * m <= p * n.
Proof.
intros n m p H1 H2. le_elim H1.
le_elim H2. le_less. now apply -> NZtimes_lt_mono_neg_l.
le_equal; now rewrite H2.
le_equal; rewrite H1; now do 2 rewrite NZtimes_0_l.
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
apply -> NZeq_dne; intro H3. apply -> NZneq_lt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * m < p * n); [now apply -> NZtimes_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
assert (H4 : p * n < p * m); [now apply -> NZtimes_lt_mono_neg_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
false_hyp H2 H.
apply -> NZeq_dne; intro H3. apply -> NZneq_lt_gt_cases in H3. destruct H3 as [H3 | H3].
assert (H4 : p * n < p * m); [now apply -> NZtimes_lt_mono_pos_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
assert (H4 : p * m < p * n); [now apply -> NZtimes_lt_mono_pos_l |].
rewrite H1 in H4; false_hyp H4 NZlt_irrefl.
now rewrite H1.
Qed.

Theorem NZtimes_le_mono_pos_l : forall n m p : NZ, 0 < p -> (n <= m <-> p * n <= p * m).
Proof.
intros n m p H; do 2 rewrite NZle_lt_or_eq.
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
intros n m p H; do 2 rewrite NZle_lt_or_eq.
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

Theorem NZtimes_lt_mono :
  forall n m p q : NZ, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof.
intros n m p q H1 H2 H3 H4.
apply NZle_lt_trans with (m * p).
apply NZtimes_le_mono_nonneg_r; [assumption | now le_less].
apply -> NZtimes_lt_mono_pos_l; [assumption | now apply NZle_lt_trans with n].
Qed.

(* There are still many variants of the theorem above. One can assume 0 < n
or 0 < p or n <= m or p <= q. *)

Theorem NZtimes_le_mono :
  forall n m p q : NZ, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof.
intros n m p q H1 H2 H3 H4.
le_elim H2; le_elim H4.
le_less; now apply NZtimes_lt_mono.
rewrite <- H4; apply NZtimes_le_mono_nonneg_r; [assumption | now le_less].
rewrite <- H2; apply NZtimes_le_mono_nonneg_l; [assumption | now le_less].
rewrite H2; rewrite H4; now le_equal.
Qed.

Theorem NZtimes_pos_pos : forall n m : NZ, 0 < n -> 0 < m -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_pos_r.
Qed.

Theorem NZtimes_nonneg_nonneg : forall n m : NZ, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply NZtimes_le_mono_nonneg_r.
Qed.

Theorem NZtimes_neg_neg : forall n m : NZ, n < 0 -> m < 0 -> 0 < n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_neg_r.
Qed.

Theorem NZtimes_nonpos_nonpos : forall n m : NZ, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply NZtimes_le_mono_nonpos_r.
Qed.

Theorem NZtimes_pos_neg : forall n m : NZ, 0 < n -> m < 0 -> n * m < 0.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply -> NZtimes_lt_mono_neg_r.
Qed.

Theorem NZtimes_nonneg_nonpos : forall n m : NZ, 0 <= n -> m <= 0 -> n * m <= 0.
Proof.
intros n m H1 H2.
rewrite <- (NZtimes_0_l m). now apply NZtimes_le_mono_nonpos_r.
Qed.

Theorem NZtimes_neg_pos : forall n m : NZ, n < 0 -> 0 < m -> n * m < 0.
Proof.
intros; rewrite NZtimes_comm; now apply NZtimes_pos_neg.
Qed.

Theorem NZtimes_nonpos_nonneg : forall n m : NZ, n <= 0 -> 0 <= m -> n * m <= 0.
Proof.
intros; rewrite NZtimes_comm; now apply NZtimes_nonneg_nonpos.
Qed.

Theorem NZtimes_eq_0 : forall n m : NZ, n * m == 0 -> n == 0 \/ m == 0.
Proof.
intros n m H; destruct (NZlt_trichotomy n 0) as [H1 | [H1 | H1]];
destruct (NZlt_trichotomy m 0) as [H2 | [H2 | H2]];
try (now right); try (now left).
elimtype False; now apply (NZlt_neq 0 (n * m)); [apply NZtimes_neg_neg |].
elimtype False; now apply (NZlt_neq (n * m) 0); [apply NZtimes_neg_pos |].
elimtype False; now apply (NZlt_neq (n * m) 0); [apply NZtimes_pos_neg |].
elimtype False; now apply (NZlt_neq 0 (n * m)); [apply NZtimes_pos_pos |].
Qed.

Theorem NZtimes_neq_0 : forall n m : NZ, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof.
intros n m; split; intro H.
intro H1; apply NZtimes_eq_0 in H1. tauto.
split; intro H1; rewrite H1 in H;
(rewrite NZtimes_0_l in H || rewrite NZtimes_0_r in H); now apply H.
Qed.

Theorem NZtimes_pos : forall n m : NZ, 0 < n * m <-> (0 < n /\ 0 < m) \/ (m < 0 /\ n < 0).
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

Theorem NZtimes_neg :
  forall n m : NZ, n * m < 0 <-> (n < 0 /\ m > 0) \/ (n > 0 /\ m < 0).
Proof.
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (NZlt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite NZtimes_0_l in H; false_hyp H NZlt_irrefl |];
(destruct (NZlt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite NZtimes_0_r in H; false_hyp H NZlt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m > 0) by now apply NZtimes_neg_neg.
elimtype False; now apply (NZlt_asymm (n * m) 0).
assert (H3 : n * m > 0) by now apply NZtimes_pos_pos.
elimtype False; now apply (NZlt_asymm (n * m) 0).
now apply NZtimes_neg_pos. now apply NZtimes_pos_neg.
Qed.

End NZTimesOrderPropFunct.
