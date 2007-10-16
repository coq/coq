Require Export NOrder.

Module NTimesOrderPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NOrderPropMod := NOrderPropFunct NAxiomsMod.
Open Local Scope NatIntScope.

Theorem plus_lt_mono_l : forall n m p : N, n < m <-> p + n < p + m.
Proof NZplus_lt_mono_l.

Theorem plus_lt_mono_r : forall n m p : N, n < m <-> n + p < m + p.
Proof NZplus_lt_mono_r.

Theorem plus_lt_mono : forall n m p q : N, n < m -> p < q -> n + p < m + q.
Proof NZplus_lt_mono.

Theorem plus_le_mono_l : forall n m p : N, n <= m <-> p + n <= p + m.
Proof NZplus_le_mono_l.

Theorem plus_le_mono_r : forall n m p : N, n <= m <-> n + p <= m + p.
Proof NZplus_le_mono_r.

Theorem plus_le_mono : forall n m p q : N, n <= m -> p <= q -> n + p <= m + q.
Proof NZplus_le_mono.

Theorem plus_lt_le_mono : forall n m p q : N, n < m -> p <= q -> n + p < m + q.
Proof NZplus_lt_le_mono.

Theorem plus_le_lt_mono : forall n m p q : N, n <= m -> p < q -> n + p < m + q.
Proof NZplus_le_lt_mono.

Theorem plus_pos_pos : forall n m : N, 0 < n -> 0 < m -> 0 < n + m.
Proof NZplus_pos_pos.

Theorem lt_plus_pos_l : forall n m : N, 0 < n -> m < n + m.
Proof NZlt_plus_pos_l.

Theorem lt_plus_pos_r : forall n m : N, 0 < n -> m < m + n.
Proof NZlt_plus_pos_r.

Theorem le_lt_plus_lt : forall n m p q : N, n <= m -> p + m < q + n -> p < q.
Proof NZle_lt_plus_lt.

Theorem lt_le_plus_lt : forall n m p q : N, n < m -> p + m <= q + n -> p < q.
Proof NZlt_le_plus_lt.

Theorem le_le_plus_le : forall n m p q : N, n <= m -> p + m <= q + n -> p <= q.
Proof NZle_le_plus_le.

Theorem plus_lt_cases : forall n m p q : N, n + m < p + q -> n < p \/ m < q.
Proof NZplus_lt_cases.

Theorem plus_le_cases : forall n m p q : N, n + m <= p + q -> n <= p \/ m <= q.
Proof NZplus_le_cases.

Theorem plus_pos_cases : forall n m : N, 0 < n + m -> 0 < n \/ 0 < m.
Proof NZplus_pos_cases.

(** Theorems true for natural numbers *)

Theorem le_plus_r : forall n m : N, n <= n + m.
Proof.
intro n; induct m.
rewrite plus_0_r; le_equal.
intros m IH. rewrite plus_succ_r; now apply le_le_succ.
Qed.

Theorem lt_lt_plus_r : forall n m p : N, n < m -> n < m + p.
Proof.
intros n m p H; rewrite <- (plus_0_r n).
apply plus_lt_le_mono; [assumption | apply le_0_l].
Qed.

Theorem lt_lt_plus_l : forall n m p : N, n < m -> n < p + m.
Proof.
intros n m p; rewrite plus_comm; apply lt_lt_plus_r.
Qed.

Theorem plus_pos_l : forall n m : N, 0 < n -> 0 < n + m.
Proof.
intros; apply NZplus_pos_nonneg. assumption. apply le_0_l.
Qed.

Theorem plus_pos_r : forall n m : N, 0 < m -> 0 < n + m.
Proof.
intros; apply NZplus_nonneg_pos. apply le_0_l. assumption.
Qed.

(* The following property is similar to plus_repl_pair in NPlus.v
and is used to prove the correctness of the definition of order
on integers constructed from pairs of natural numbers *)

Theorem plus_lt_repl_pair : forall n m n' m' u v,
  n + u < m + v -> n + m' == n' + m -> n' + u < m' + v.
Proof.
intros n m n' m' u v H1 H2.
symmetry in H2. assert (H3 : n' + m <= n + m'); [now le_equal |].
assert (H4 : n + u + (n' + m) < m + v + (n + m')); [now apply plus_lt_le_mono |].
stepl (n + (m + (n' + u))) in H4 by ring. stepr (n + (m + (m' + v))) in H4 by ring.
now do 2 apply <- plus_lt_mono_l in H4.
Qed.

(** Multiplication and order *)

Theorem times_lt_pred :
  forall p q n m : N, S p == q -> (p * n < p * m <-> q * n + m < q * m + n).
Proof NZtimes_lt_pred.

Theorem times_lt_mono_pos_l : forall p n m : N, 0 < p -> (n < m <-> p * n < p * m).
Proof NZtimes_lt_mono_pos_l.

Theorem times_lt_mono_pos_r : forall p n m : N, 0 < p -> (n < m <-> n * p < m * p).
Proof NZtimes_lt_mono_pos_r.

Theorem times_le_mono_l : forall n m p : N, n <= m -> p * n <= p * m.
Proof.
intros; apply NZtimes_le_mono_nonneg_l. apply le_0_l. assumption.
Qed.

Theorem times_le_mono_r : forall n m p : N, n <= m -> n * p <= m * p.
Proof.
intros; apply NZtimes_le_mono_nonneg_r. apply le_0_l. assumption.
Qed.

Theorem times_cancel_l : forall n m p : N, p ~= 0 -> (p * n == p * m <-> n == m).
Proof NZtimes_cancel_l.

Theorem times_le_mono_pos_l : forall n m p : N, 0 < p -> (n <= m <-> p * n <= p * m).
Proof NZtimes_le_mono_pos_l.

Theorem times_le_mono_pos_r : forall n m p : N, 0 < p -> (n <= m <-> n * p <= m * p).
Proof NZtimes_le_mono_pos_r.

Theorem times_lt_mono : forall n m p q : N, n < m -> p < q -> n * p < m * q.
Proof.
intros; apply NZtimes_lt_mono; try assumption; apply le_0_l.
Qed.

Theorem times_le_mono : forall n m p q : N, n <= m -> p <= q -> n * p <= m * q.
Proof.
intros; apply NZtimes_le_mono; try assumption; apply le_0_l.
Qed.

Theorem Ztimes_pos_pos : forall n m : N, 0 < n -> 0 < m -> 0 < n * m.
Proof NZtimes_pos_pos.

Theorem times_eq_0 : forall n m : N, n * m == 0 -> n == 0 \/ m == 0.
Proof NZtimes_eq_0.

Theorem times_neq_0 : forall n m : N, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZtimes_neq_0.

Theorem times_2_mono_l : forall n m : N, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof NZtimes_2_mono_l.

Theorem times_pos : forall n m : N, n * m > 0 <-> n > 0 /\ m > 0.
Proof.
intros n m; split; [intro H | intros [H1 H2]].
apply -> NZtimes_pos in H. destruct H as [[H1 H2] | [H1 H2]]. now split. false_hyp H1 nlt_0_r.
now apply NZtimes_pos_pos.
Qed.

End NTimesOrderPropFunct.

