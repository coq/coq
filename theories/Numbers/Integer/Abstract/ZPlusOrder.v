Require Export ZOrder.

Module ZPlusOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZOrderPropMod := ZOrderPropFunct ZAxiomsMod.
Open Local Scope NatIntScope.

(** Theorems that are true on both natural numbers and integers *)

Theorem Zplus_lt_mono_l : forall n m p : Z, n < m <-> p + n < p + m.
Proof NZplus_lt_mono_l.

Theorem Zplus_lt_mono_r : forall n m p : Z, n < m <-> n + p < m + p.
Proof NZplus_lt_mono_r.

Theorem Zplus_lt_mono : forall n m p q : Z, n < m -> p < q -> n + p < m + q.
Proof NZplus_lt_mono.

Theorem Zplus_le_mono_l : forall n m p : Z, n <= m <-> p + n <= p + m.
Proof NZplus_le_mono_l.

Theorem Zplus_le_mono_r : forall n m p : Z, n <= m <-> n + p <= m + p.
Proof NZplus_le_mono_r.

Theorem Zplus_le_mono : forall n m p q : Z, n <= m -> p <= q -> n + p <= m + q.
Proof NZplus_le_mono.

Theorem Zplus_lt_le_mono : forall n m p q : Z, n < m -> p <= q -> n + p < m + q.
Proof NZplus_lt_le_mono.

Theorem Zplus_le_lt_mono : forall n m p q : Z, n <= m -> p < q -> n + p < m + q.
Proof NZplus_le_lt_mono.

Theorem Zplus_pos_pos : forall n m : Z, 0 < n -> 0 < m -> 0 < n + m.
Proof NZplus_pos_pos.

Theorem Zplus_pos_nonneg : forall n m : Z, 0 < n -> 0 <= m -> 0 < n + m.
Proof NZplus_pos_nonneg.

Theorem Zplus_nonneg_pos : forall n m : Z, 0 <= n -> 0 < m -> 0 < n + m.
Proof NZplus_nonneg_pos.

Theorem Zplus_nonneg_nonneg : forall n m : Z, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof NZplus_nonneg_nonneg.

Theorem Zlt_plus_pos_l : forall n m : Z, 0 < n -> m < n + m.
Proof NZlt_plus_pos_l.

Theorem Zlt_plus_pos_r : forall n m : Z, 0 < n -> m < m + n.
Proof NZlt_plus_pos_r.

Theorem Zle_lt_plus_lt : forall n m p q : Z, n <= m -> p + m < q + n -> p < q.
Proof NZle_lt_plus_lt.

Theorem Zlt_le_plus_lt : forall n m p q : Z, n < m -> p + m <= q + n -> p < q.
Proof NZlt_le_plus_lt.

Theorem Zle_le_plus_le : forall n m p q : Z, n <= m -> p + m <= q + n -> p <= q.
Proof NZle_le_plus_le.

Theorem Zplus_lt_cases : forall n m p q : Z, n + m < p + q -> n < p \/ m < q.
Proof NZplus_lt_cases.

Theorem Zplus_le_cases : forall n m p q : Z, n + m <= p + q -> n <= p \/ m <= q.
Proof NZplus_le_cases.

Theorem Zplus_neg_cases : forall n m : Z, n + m < 0 -> n < 0 \/ m < 0.
Proof NZplus_neg_cases.

Theorem Zplus_pos_cases : forall n m : Z, 0 < n + m -> 0 < n \/ 0 < m.
Proof NZplus_pos_cases.

Theorem Zplus_nonpos_cases : forall n m : Z, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof NZplus_nonpos_cases.

Theorem Zplus_nonneg_cases : forall n m : Z, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof NZplus_nonneg_cases.

(** Theorems that are either not valid on N or have different proofs on N and Z *)

(** Minus and order *)

Theorem Zlt_lt_minus : forall n m : Z, n < m <-> 0 < m - n.
Proof.
intros n m. stepr (0 + n < m - n + n) by symmetry; apply Zplus_lt_mono_r.
rewrite Zplus_0_l; now rewrite Zminus_plus_diag.
Qed.

Theorem Zle_le_minus : forall n m : Z, n <= m <-> 0 <= m - n.
Proof.
intros n m; stepr (0 + n <= m - n + n) by symmetry; apply Zplus_le_mono_r.
rewrite Zplus_0_l; now rewrite Zminus_plus_diag.
Qed.

Theorem Zopp_lt_mono : forall n m : Z, n < m <-> - m < - n.
Proof.
intros n m. stepr (m + - m < m + - n) by symmetry; apply Zplus_lt_mono_l.
do 2 rewrite Zplus_opp_minus. rewrite Zminus_diag. apply Zlt_lt_minus.
Qed.

Theorem Zopp_le_mono : forall n m : Z, n <= m <-> - m <= - n.
Proof.
intros n m. stepr (m + - m <= m + - n) by symmetry; apply Zplus_le_mono_l.
do 2 rewrite Zplus_opp_minus. rewrite Zminus_diag. apply Zle_le_minus.
Qed.

Theorem Zopp_pos_neg : forall n : Z, 0 < - n <-> n < 0.
Proof.
intro n; rewrite (Zopp_lt_mono n 0); now rewrite Zopp_0.
Qed.

Theorem Zopp_neg_pos : forall n : Z, - n < 0 <-> 0 < n.
Proof.
intro n. rewrite (Zopp_lt_mono 0 n). now rewrite Zopp_0.
Qed.

Theorem Zopp_nonneg_nonpos : forall n : Z, 0 <= - n <-> n <= 0.
Proof.
intro n; rewrite (Zopp_le_mono n 0); now rewrite Zopp_0.
Qed.

Theorem Zopp_nonpos_nonneg : forall n : Z, - n <= 0 <-> 0 <= n.
Proof.
intro n. rewrite (Zopp_le_mono 0 n). now rewrite Zopp_0.
Qed.

Theorem Zminus_lt_mono_l : forall n m p : Z, n < m <-> p - m < p - n.
Proof.
intros n m p. do 2 rewrite <- Zplus_opp_minus. rewrite <- Zplus_lt_mono_l.
apply Zopp_lt_mono.
Qed.

Theorem Zminus_lt_mono_r : forall n m p : Z, n < m <-> n - p < m - p.
Proof.
intros n m p; do 2 rewrite <- Zplus_opp_minus; apply Zplus_lt_mono_r.
Qed.

Theorem Zminus_lt_mono : forall n m p q : Z, n < m -> q < p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply NZlt_trans with (m - p);
[now apply -> Zminus_lt_mono_r | now apply -> Zminus_lt_mono_l].
Qed.

Theorem Zminus_le_mono_l : forall n m p : Z, n <= m <-> p - m <= p - n.
Proof.
intros n m p; do 2 rewrite <- Zplus_opp_minus; rewrite <- Zplus_le_mono_l;
apply Zopp_le_mono.
Qed.

Theorem Zminus_le_mono_r : forall n m p : Z, n <= m <-> n - p <= m - p.
Proof.
intros n m p; do 2 rewrite <- Zplus_opp_minus; apply Zplus_le_mono_r.
Qed.

Theorem Zminus_le_mono : forall n m p q : Z, n <= m -> q <= p -> n - p <= m - q.
Proof.
intros n m p q H1 H2.
apply NZle_trans with (m - p);
[now apply -> Zminus_le_mono_r | now apply -> Zminus_le_mono_l].
Qed.

Theorem Zminus_lt_le_mono : forall n m p q : Z, n < m -> q <= p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply NZlt_le_trans with (m - p);
[now apply -> Zminus_lt_mono_r | now apply -> Zminus_le_mono_l].
Qed.

Theorem Zminus_le_lt_mono : forall n m p q : Z, n <= m -> q < p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply NZle_lt_trans with (m - p);
[now apply -> Zminus_le_mono_r | now apply -> Zminus_lt_mono_l].
Qed.

Theorem Zle_lt_minus_lt : forall n m p q : Z, n <= m -> p - n < q - m -> p < q.
Proof.
intros n m p q H1 H2. apply (Zle_lt_plus_lt (- m) (- n));
[now apply -> Zopp_le_mono | now do 2 rewrite Zplus_opp_minus].
Qed.

Theorem Zlt_le_minus_lt : forall n m p q : Z, n < m -> p - n <= q - m -> p < q.
Proof.
intros n m p q H1 H2. apply (Zlt_le_plus_lt (- m) (- n));
[now apply -> Zopp_lt_mono | now do 2 rewrite Zplus_opp_minus].
Qed.

Theorem Zle_le_minus_lt : forall n m p q : Z, n <= m -> p - n <= q - m -> p <= q.
Proof.
intros n m p q H1 H2. apply (Zle_le_plus_le (- m) (- n));
[now apply -> Zopp_le_mono | now do 2 rewrite Zplus_opp_minus].
Qed.

Theorem Zlt_plus_lt_minus_r : forall n m p : Z, n + p < m <-> n < m - p.
Proof.
intros n m p. stepl (n + p - p < m - p) by symmetry; apply Zminus_lt_mono_r.
now rewrite Zplus_minus_diag.
Qed.

Theorem Zle_plus_le_minus_r : forall n m p : Z, n + p <= m <-> n <= m - p.
Proof.
intros n m p. stepl (n + p - p <= m - p) by symmetry; apply Zminus_le_mono_r.
now rewrite Zplus_minus_diag.
Qed.

Theorem Zlt_plus_lt_minus_l : forall n m p : Z, n + p < m <-> p < m - n.
Proof.
intros n m p. rewrite Zplus_comm; apply Zlt_plus_lt_minus_r.
Qed.

Theorem Zle_plus_le_minus_l : forall n m p : Z, n + p <= m <-> p <= m - n.
Proof.
intros n m p. rewrite Zplus_comm; apply Zle_plus_le_minus_r.
Qed.

Theorem Zlt_minus_lt_plus_r : forall n m p : Z, n - p < m <-> n < m + p.
Proof.
intros n m p. stepl (n - p + p < m + p) by symmetry; apply Zplus_lt_mono_r.
now rewrite Zminus_plus_diag.
Qed.

Theorem Zle_minus_le_plus_r : forall n m p : Z, n - p <= m <-> n <= m + p.
Proof.
intros n m p. stepl (n - p + p <= m + p) by symmetry; apply Zplus_le_mono_r.
now rewrite Zminus_plus_diag.
Qed.

Theorem Zlt_minus_lt_plus_l : forall n m p : Z, n - m < p <-> n < m + p.
Proof.
intros n m p. rewrite Zplus_comm; apply Zlt_minus_lt_plus_r.
Qed.

Theorem Zle_minus_le_plus_l : forall n m p : Z, n - m <= p <-> n <= m + p.
Proof.
intros n m p. rewrite Zplus_comm; apply Zle_minus_le_plus_r.
Qed.

Theorem Zlt_minus_lt_plus : forall n m p q : Z, n - m < p - q <-> n + q < m + p.
Proof.
intros n m p q. rewrite Zlt_minus_lt_plus_l. rewrite Zplus_minus_assoc.
now rewrite <- Zlt_plus_lt_minus_r.
Qed.

Theorem Zle_minus_le_plus : forall n m p q : Z, n - m <= p - q <-> n + q <= m + p.
Proof.
intros n m p q. rewrite Zle_minus_le_plus_l. rewrite Zplus_minus_assoc.
now rewrite <- Zle_plus_le_minus_r.
Qed.

Theorem Zlt_minus_pos : forall n m : Z, 0 < m <-> n - m < n.
Proof.
intros n m. stepr (n - m < n - 0) by now rewrite Zminus_0_r. apply Zminus_lt_mono_l.
Qed.

Theorem Zle_minus_nonneg : forall n m : Z, 0 <= m <-> n - m <= n.
Proof.
intros n m. stepr (n - m <= n - 0) by now rewrite Zminus_0_r. apply Zminus_le_mono_l.
Qed.

Theorem Zminus_lt_cases : forall n m p q : Z, n - m < p - q -> n < m \/ q < p.
Proof.
intros n m p q H. rewrite Zlt_minus_lt_plus in H. now apply Zplus_lt_cases.
Qed.

Theorem Zminus_le_cases : forall n m p q : Z, n - m <= p - q -> n <= m \/ q <= p.
Proof.
intros n m p q H. rewrite Zle_minus_le_plus in H. now apply Zplus_le_cases.
Qed.

Theorem Zminus_neg_cases : forall n m : Z, n - m < 0 -> n < 0 \/ 0 < m.
Proof.
intros n m H; rewrite <- Zplus_opp_minus in H.
setoid_replace (0 < m) with (- m < 0) using relation iff by (symmetry; apply Zopp_neg_pos).
now apply Zplus_neg_cases.
Qed.

Theorem Zminus_pos_cases : forall n m : Z, 0 < n - m -> 0 < n \/ m < 0.
Proof.
intros n m H; rewrite <- Zplus_opp_minus in H.
setoid_replace (m < 0) with (0 < - m) using relation iff by (symmetry; apply Zopp_pos_neg).
now apply Zplus_pos_cases.
Qed.

Theorem Zminus_nonpos_cases : forall n m : Z, n - m <= 0 -> n <= 0 \/ 0 <= m.
Proof.
intros n m H; rewrite <- Zplus_opp_minus in H.
setoid_replace (0 <= m) with (- m <= 0) using relation iff by (symmetry; apply Zopp_nonpos_nonneg).
now apply Zplus_nonpos_cases.
Qed.

Theorem Zminus_nonneg_cases : forall n m : Z, 0 <= n - m -> 0 <= n \/ m <= 0.
Proof.
intros n m H; rewrite <- Zplus_opp_minus in H.
setoid_replace (m <= 0) with (0 <= - m) using relation iff by (symmetry; apply Zopp_nonneg_nonpos).
now apply Zplus_nonneg_cases.
Qed.

End ZPlusOrderPropFunct.


