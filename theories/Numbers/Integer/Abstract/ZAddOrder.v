(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export ZLt.

Module ZAddOrderPropFunct (Import Z : ZAxiomsSig').
Include ZOrderPropFunct Z.

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

Theorem add_neg_neg : forall n m, n < 0 -> m < 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_mono.
Qed.

Theorem add_neg_nonpos : forall n m, n < 0 -> m <= 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_le_mono.
Qed.

Theorem add_nonpos_neg : forall n m, n <= 0 -> m < 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_lt_mono.
Qed.

Theorem add_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> n + m <= 0.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_mono.
Qed.

(** Sub and order *)

Theorem lt_0_sub : forall n m, 0 < m - n <-> n < m.
Proof.
intros n m. stepl (0 + n < m - n + n) by symmetry; apply add_lt_mono_r.
rewrite add_0_l; now rewrite sub_simpl_r.
Qed.

Notation sub_pos := lt_0_sub (only parsing).

Theorem le_0_sub : forall n m, 0 <= m - n <-> n <= m.
Proof.
intros n m; stepl (0 + n <= m - n + n) by symmetry; apply add_le_mono_r.
rewrite add_0_l; now rewrite sub_simpl_r.
Qed.

Notation sub_nonneg := le_0_sub (only parsing).

Theorem lt_sub_0 : forall n m, n - m < 0 <-> n < m.
Proof.
intros n m. stepl (n - m + m < 0 + m) by symmetry; apply add_lt_mono_r.
rewrite add_0_l; now rewrite sub_simpl_r.
Qed.

Notation sub_neg := lt_sub_0 (only parsing).

Theorem le_sub_0 : forall n m, n - m <= 0 <-> n <= m.
Proof.
intros n m. stepl (n - m + m <= 0 + m) by symmetry; apply add_le_mono_r.
rewrite add_0_l; now rewrite sub_simpl_r.
Qed.

Notation sub_nonpos := le_sub_0 (only parsing).

Theorem opp_lt_mono : forall n m, n < m <-> - m < - n.
Proof.
intros n m. stepr (m + - m < m + - n) by symmetry; apply add_lt_mono_l.
do 2 rewrite add_opp_r. rewrite sub_diag. symmetry; apply lt_0_sub.
Qed.

Theorem opp_le_mono : forall n m, n <= m <-> - m <= - n.
Proof.
intros n m. stepr (m + - m <= m + - n) by symmetry; apply add_le_mono_l.
do 2 rewrite add_opp_r. rewrite sub_diag. symmetry; apply le_0_sub.
Qed.

Theorem opp_pos_neg : forall n, 0 < - n <-> n < 0.
Proof.
intro n; rewrite (opp_lt_mono n 0); now rewrite opp_0.
Qed.

Theorem opp_neg_pos : forall n, - n < 0 <-> 0 < n.
Proof.
intro n. rewrite (opp_lt_mono 0 n). now rewrite opp_0.
Qed.

Theorem opp_nonneg_nonpos : forall n, 0 <= - n <-> n <= 0.
Proof.
intro n; rewrite (opp_le_mono n 0); now rewrite opp_0.
Qed.

Theorem opp_nonpos_nonneg : forall n, - n <= 0 <-> 0 <= n.
Proof.
intro n. rewrite (opp_le_mono 0 n). now rewrite opp_0.
Qed.

Theorem sub_lt_mono_l : forall n m p, n < m <-> p - m < p - n.
Proof.
intros n m p. do 2 rewrite <- add_opp_r. rewrite <- add_lt_mono_l.
apply opp_lt_mono.
Qed.

Theorem sub_lt_mono_r : forall n m p, n < m <-> n - p < m - p.
Proof.
intros n m p; do 2 rewrite <- add_opp_r; apply add_lt_mono_r.
Qed.

Theorem sub_lt_mono : forall n m p q, n < m -> q < p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply lt_trans with (m - p);
[now apply -> sub_lt_mono_r | now apply -> sub_lt_mono_l].
Qed.

Theorem sub_le_mono_l : forall n m p, n <= m <-> p - m <= p - n.
Proof.
intros n m p; do 2 rewrite <- add_opp_r; rewrite <- add_le_mono_l;
apply opp_le_mono.
Qed.

Theorem sub_le_mono_r : forall n m p, n <= m <-> n - p <= m - p.
Proof.
intros n m p; do 2 rewrite <- add_opp_r; apply add_le_mono_r.
Qed.

Theorem sub_le_mono : forall n m p q, n <= m -> q <= p -> n - p <= m - q.
Proof.
intros n m p q H1 H2.
apply le_trans with (m - p);
[now apply -> sub_le_mono_r | now apply -> sub_le_mono_l].
Qed.

Theorem sub_lt_le_mono : forall n m p q, n < m -> q <= p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply lt_le_trans with (m - p);
[now apply -> sub_lt_mono_r | now apply -> sub_le_mono_l].
Qed.

Theorem sub_le_lt_mono : forall n m p q, n <= m -> q < p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply le_lt_trans with (m - p);
[now apply -> sub_le_mono_r | now apply -> sub_lt_mono_l].
Qed.

Theorem le_lt_sub_lt : forall n m p q, n <= m -> p - n < q - m -> p < q.
Proof.
intros n m p q H1 H2. apply (le_lt_add_lt (- m) (- n));
[now apply -> opp_le_mono | now do 2 rewrite add_opp_r].
Qed.

Theorem lt_le_sub_lt : forall n m p q, n < m -> p - n <= q - m -> p < q.
Proof.
intros n m p q H1 H2. apply (lt_le_add_lt (- m) (- n));
[now apply -> opp_lt_mono | now do 2 rewrite add_opp_r].
Qed.

Theorem le_le_sub_lt : forall n m p q, n <= m -> p - n <= q - m -> p <= q.
Proof.
intros n m p q H1 H2. apply (le_le_add_le (- m) (- n));
[now apply -> opp_le_mono | now do 2 rewrite add_opp_r].
Qed.

Theorem lt_add_lt_sub_r : forall n m p, n + p < m <-> n < m - p.
Proof.
intros n m p. stepl (n + p - p < m - p) by symmetry; apply sub_lt_mono_r.
now rewrite add_simpl_r.
Qed.

Theorem le_add_le_sub_r : forall n m p, n + p <= m <-> n <= m - p.
Proof.
intros n m p. stepl (n + p - p <= m - p) by symmetry; apply sub_le_mono_r.
now rewrite add_simpl_r.
Qed.

Theorem lt_add_lt_sub_l : forall n m p, n + p < m <-> p < m - n.
Proof.
intros n m p. rewrite add_comm; apply lt_add_lt_sub_r.
Qed.

Theorem le_add_le_sub_l : forall n m p, n + p <= m <-> p <= m - n.
Proof.
intros n m p. rewrite add_comm; apply le_add_le_sub_r.
Qed.

Theorem lt_sub_lt_add_r : forall n m p, n - p < m <-> n < m + p.
Proof.
intros n m p. stepl (n - p + p < m + p) by symmetry; apply add_lt_mono_r.
now rewrite sub_simpl_r.
Qed.

Theorem le_sub_le_add_r : forall n m p, n - p <= m <-> n <= m + p.
Proof.
intros n m p. stepl (n - p + p <= m + p) by symmetry; apply add_le_mono_r.
now rewrite sub_simpl_r.
Qed.

Theorem lt_sub_lt_add_l : forall n m p, n - m < p <-> n < m + p.
Proof.
intros n m p. rewrite add_comm; apply lt_sub_lt_add_r.
Qed.

Theorem le_sub_le_add_l : forall n m p, n - m <= p <-> n <= m + p.
Proof.
intros n m p. rewrite add_comm; apply le_sub_le_add_r.
Qed.

Theorem lt_sub_lt_add : forall n m p q, n - m < p - q <-> n + q < m + p.
Proof.
intros n m p q. rewrite lt_sub_lt_add_l. rewrite add_sub_assoc.
now rewrite <- lt_add_lt_sub_r.
Qed.

Theorem le_sub_le_add : forall n m p q, n - m <= p - q <-> n + q <= m + p.
Proof.
intros n m p q. rewrite le_sub_le_add_l. rewrite add_sub_assoc.
now rewrite <- le_add_le_sub_r.
Qed.

Theorem lt_sub_pos : forall n m, 0 < m <-> n - m < n.
Proof.
intros n m. stepr (n - m < n - 0) by now rewrite sub_0_r. apply sub_lt_mono_l.
Qed.

Theorem le_sub_nonneg : forall n m, 0 <= m <-> n - m <= n.
Proof.
intros n m. stepr (n - m <= n - 0) by now rewrite sub_0_r. apply sub_le_mono_l.
Qed.

Theorem sub_lt_cases : forall n m p q, n - m < p - q -> n < m \/ q < p.
Proof.
intros n m p q H. rewrite lt_sub_lt_add in H. now apply add_lt_cases.
Qed.

Theorem sub_le_cases : forall n m p q, n - m <= p - q -> n <= m \/ q <= p.
Proof.
intros n m p q H. rewrite le_sub_le_add in H. now apply add_le_cases.
Qed.

Theorem sub_neg_cases : forall n m, n - m < 0 -> n < 0 \/ 0 < m.
Proof.
intros n m H; rewrite <- add_opp_r in H.
setoid_replace (0 < m) with (- m < 0) using relation iff by (symmetry; apply opp_neg_pos).
now apply add_neg_cases.
Qed.

Theorem sub_pos_cases : forall n m, 0 < n - m -> 0 < n \/ m < 0.
Proof.
intros n m H; rewrite <- add_opp_r in H.
setoid_replace (m < 0) with (0 < - m) using relation iff by (symmetry; apply opp_pos_neg).
now apply add_pos_cases.
Qed.

Theorem sub_nonpos_cases : forall n m, n - m <= 0 -> n <= 0 \/ 0 <= m.
Proof.
intros n m H; rewrite <- add_opp_r in H.
setoid_replace (0 <= m) with (- m <= 0) using relation iff by (symmetry; apply opp_nonpos_nonneg).
now apply add_nonpos_cases.
Qed.

Theorem sub_nonneg_cases : forall n m, 0 <= n - m -> 0 <= n \/ m <= 0.
Proof.
intros n m H; rewrite <- add_opp_r in H.
setoid_replace (m <= 0) with (0 <= - m) using relation iff by (symmetry; apply opp_nonneg_nonpos).
now apply add_nonneg_cases.
Qed.

Section PosNeg.

Variable P : Z.t -> Prop.
Hypothesis P_wd : Proper (Z.eq ==> iff) P.

Theorem zero_pos_neg :
  P 0 -> (forall n, 0 < n -> P n /\ P (- n)) -> forall n, P n.
Proof.
intros H1 H2 n. destruct (lt_trichotomy n 0) as [H3 | [H3 | H3]].
apply <- opp_pos_neg in H3. apply H2 in H3. destruct H3 as [_ H3].
now rewrite opp_involutive in H3.
now rewrite H3.
apply H2 in H3; now destruct H3.
Qed.

End PosNeg.

Ltac zero_pos_neg n := induction_maker n ltac:(apply zero_pos_neg).

End ZAddOrderPropFunct.


