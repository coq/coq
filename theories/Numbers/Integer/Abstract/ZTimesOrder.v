Require Export ZPlusOrder.

Module ZTimesOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZPlusOrderPropMod := ZPlusOrderPropFunct ZAxiomsMod.
Open Local Scope IntScope.

(** Theorems that are true on both natural numbers and integers *)

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

Theorem Ztimes_le_mono_pos_l : forall n m p : Z, 0 < p -> (n <= m <-> p * n <= p * m).
Proof NZtimes_le_mono_pos_l.

Theorem Ztimes_le_mono_pos_r : forall n m p : Z, 0 < p -> (n <= m <-> n * p <= m * p).
Proof NZtimes_le_mono_pos_r.

Theorem Ztimes_le_mono_neg_l : forall n m p : Z, p < 0 -> (n <= m <-> p * m <= p * n).
Proof NZtimes_le_mono_neg_l.

Theorem Ztimes_le_mono_neg_r : forall n m p : Z, p < 0 -> (n <= m <-> m * p <= n * p).
Proof NZtimes_le_mono_neg_r.

Theorem Ztimes_lt_mono :
  forall n m p q : Z, 0 <= n -> n < m -> 0 <= p -> p < q -> n * p < m * q.
Proof NZtimes_lt_mono.

Theorem Ztimes_le_mono :
  forall n m p q : Z, 0 <= n -> n <= m -> 0 <= p -> p <= q -> n * p <= m * q.
Proof NZtimes_le_mono.

Theorem Ztimes_pos_pos : forall n m : Z, 0 < n -> 0 < m -> 0 < n * m.
Proof NZtimes_pos_pos.

Theorem Ztimes_nonneg_nonneg : forall n m : Z, 0 <= n -> 0 <= m -> 0 <= n * m.
Proof NZtimes_nonneg_nonneg.

Theorem Ztimes_neg_neg : forall n m : Z, n < 0 -> m < 0 -> 0 < n * m.
Proof NZtimes_neg_neg.

Theorem Ztimes_nonpos_nonpos : forall n m : Z, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof NZtimes_nonpos_nonpos.

Theorem Ztimes_pos_neg : forall n m : Z, 0 < n -> m < 0 -> n * m < 0.
Proof NZtimes_pos_neg.

Theorem Ztimes_nonneg_nonpos : forall n m : Z, 0 <= n -> m <= 0 -> n * m <= 0.
Proof NZtimes_nonneg_nonpos.

Theorem Ztimes_neg_pos : forall n m : Z, n < 0 -> 0 < m -> n * m < 0.
Proof NZtimes_neg_pos.

Theorem Ztimes_nonpos_nonneg : forall n m : Z, n <= 0 -> 0 <= m -> n * m <= 0.
Proof NZtimes_nonpos_nonneg.

Theorem Ztimes_eq_0 : forall n m : Z, n * m == 0 -> n == 0 \/ m == 0.
Proof NZtimes_eq_0.

Theorem Ztimes_neq_0 : forall n m : Z, n ~= 0 /\ m ~= 0 <-> n * m ~= 0.
Proof NZtimes_neq_0.

Theorem Ztimes_pos : forall n m : Z, 0 < n * m <-> (0 < n /\ 0 < m) \/ (m < 0 /\ n < 0).
Proof NZtimes_pos.

Theorem Ztimes_neg :
  forall n m : Z, n * m < 0 <-> (n < 0 /\ m > 0) \/ (n > 0 /\ m < 0).
Proof NZtimes_neg.

Theorem Ztimes_2_mono_l : forall n m : Z, n < m -> 1 + (1 + 1) * n < (1 + 1) * m.
Proof NZtimes_2_mono_l.

(** Theorems that are either not valid on N or have different proofs on N and Z *)

(* None? *)

End ZTimesOrderPropFunct.

