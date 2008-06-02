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

Require Export ZLt.

Module ZPlusOrderPropFunct (Import ZAxiomsMod : ZAxiomsSig).
Module Export ZOrderPropMod := ZOrderPropFunct ZAxiomsMod.
Open Local Scope IntScope.

(* Theorems that are true on both natural numbers and integers *)

Theorem Zadd_lt_mono_l : forall n m p : Z, n < m <-> p + n < p + m.
Proof NZadd_lt_mono_l.

Theorem Zadd_lt_mono_r : forall n m p : Z, n < m <-> n + p < m + p.
Proof NZadd_lt_mono_r.

Theorem Zadd_lt_mono : forall n m p q : Z, n < m -> p < q -> n + p < m + q.
Proof NZadd_lt_mono.

Theorem Zadd_le_mono_l : forall n m p : Z, n <= m <-> p + n <= p + m.
Proof NZadd_le_mono_l.

Theorem Zadd_le_mono_r : forall n m p : Z, n <= m <-> n + p <= m + p.
Proof NZadd_le_mono_r.

Theorem Zadd_le_mono : forall n m p q : Z, n <= m -> p <= q -> n + p <= m + q.
Proof NZadd_le_mono.

Theorem Zadd_lt_le_mono : forall n m p q : Z, n < m -> p <= q -> n + p < m + q.
Proof NZadd_lt_le_mono.

Theorem Zadd_le_lt_mono : forall n m p q : Z, n <= m -> p < q -> n + p < m + q.
Proof NZadd_le_lt_mono.

Theorem Zadd_pos_pos : forall n m : Z, 0 < n -> 0 < m -> 0 < n + m.
Proof NZadd_pos_pos.

Theorem Zadd_pos_nonneg : forall n m : Z, 0 < n -> 0 <= m -> 0 < n + m.
Proof NZadd_pos_nonneg.

Theorem Zadd_nonneg_pos : forall n m : Z, 0 <= n -> 0 < m -> 0 < n + m.
Proof NZadd_nonneg_pos.

Theorem Zadd_nonneg_nonneg : forall n m : Z, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof NZadd_nonneg_nonneg.

Theorem Zlt_add_pos_l : forall n m : Z, 0 < n -> m < n + m.
Proof NZlt_add_pos_l.

Theorem Zlt_add_pos_r : forall n m : Z, 0 < n -> m < m + n.
Proof NZlt_add_pos_r.

Theorem Zle_lt_add_lt : forall n m p q : Z, n <= m -> p + m < q + n -> p < q.
Proof NZle_lt_add_lt.

Theorem Zlt_le_add_lt : forall n m p q : Z, n < m -> p + m <= q + n -> p < q.
Proof NZlt_le_add_lt.

Theorem Zle_le_add_le : forall n m p q : Z, n <= m -> p + m <= q + n -> p <= q.
Proof NZle_le_add_le.

Theorem Zadd_lt_cases : forall n m p q : Z, n + m < p + q -> n < p \/ m < q.
Proof NZadd_lt_cases.

Theorem Zadd_le_cases : forall n m p q : Z, n + m <= p + q -> n <= p \/ m <= q.
Proof NZadd_le_cases.

Theorem Zadd_neg_cases : forall n m : Z, n + m < 0 -> n < 0 \/ m < 0.
Proof NZadd_neg_cases.

Theorem Zadd_pos_cases : forall n m : Z, 0 < n + m -> 0 < n \/ 0 < m.
Proof NZadd_pos_cases.

Theorem Zadd_nonpos_cases : forall n m : Z, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof NZadd_nonpos_cases.

Theorem Zadd_nonneg_cases : forall n m : Z, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof NZadd_nonneg_cases.

(* Theorems that are either not valid on N or have different proofs on N and Z *)

Theorem Zadd_neg_neg : forall n m : Z, n < 0 -> m < 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (Zadd_0_l 0). now apply Zadd_lt_mono.
Qed.

Theorem Zadd_neg_nonpos : forall n m : Z, n < 0 -> m <= 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (Zadd_0_l 0). now apply Zadd_lt_le_mono.
Qed.

Theorem Zadd_nonpos_neg : forall n m : Z, n <= 0 -> m < 0 -> n + m < 0.
Proof.
intros n m H1 H2. rewrite <- (Zadd_0_l 0). now apply Zadd_le_lt_mono.
Qed.

Theorem Zadd_nonpos_nonpos : forall n m : Z, n <= 0 -> m <= 0 -> n + m <= 0.
Proof.
intros n m H1 H2. rewrite <- (Zadd_0_l 0). now apply Zadd_le_mono.
Qed.

(** Minus and order *)

Theorem Zlt_0_minus : forall n m : Z, 0 < m - n <-> n < m.
Proof.
intros n m. stepl (0 + n < m - n + n) by symmetry; apply Zadd_lt_mono_r.
rewrite Zadd_0_l; now rewrite Zminus_simpl_r.
Qed.

Notation Zminus_pos := Zlt_0_minus (only parsing).

Theorem Zle_0_minus : forall n m : Z, 0 <= m - n <-> n <= m.
Proof.
intros n m; stepl (0 + n <= m - n + n) by symmetry; apply Zadd_le_mono_r.
rewrite Zadd_0_l; now rewrite Zminus_simpl_r.
Qed.

Notation Zminus_nonneg := Zle_0_minus (only parsing).

Theorem Zlt_minus_0 : forall n m : Z, n - m < 0 <-> n < m.
Proof.
intros n m. stepl (n - m + m < 0 + m) by symmetry; apply Zadd_lt_mono_r.
rewrite Zadd_0_l; now rewrite Zminus_simpl_r.
Qed.

Notation Zminus_neg := Zlt_minus_0 (only parsing).

Theorem Zle_minus_0 : forall n m : Z, n - m <= 0 <-> n <= m.
Proof.
intros n m. stepl (n - m + m <= 0 + m) by symmetry; apply Zadd_le_mono_r.
rewrite Zadd_0_l; now rewrite Zminus_simpl_r.
Qed.

Notation Zminus_nonpos := Zle_minus_0 (only parsing).

Theorem Zopp_lt_mono : forall n m : Z, n < m <-> - m < - n.
Proof.
intros n m. stepr (m + - m < m + - n) by symmetry; apply Zadd_lt_mono_l.
do 2 rewrite Zadd_opp_r. rewrite Zminus_diag. symmetry; apply Zlt_0_minus.
Qed.

Theorem Zopp_le_mono : forall n m : Z, n <= m <-> - m <= - n.
Proof.
intros n m. stepr (m + - m <= m + - n) by symmetry; apply Zadd_le_mono_l.
do 2 rewrite Zadd_opp_r. rewrite Zminus_diag. symmetry; apply Zle_0_minus.
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
intros n m p. do 2 rewrite <- Zadd_opp_r. rewrite <- Zadd_lt_mono_l.
apply Zopp_lt_mono.
Qed.

Theorem Zminus_lt_mono_r : forall n m p : Z, n < m <-> n - p < m - p.
Proof.
intros n m p; do 2 rewrite <- Zadd_opp_r; apply Zadd_lt_mono_r.
Qed.

Theorem Zminus_lt_mono : forall n m p q : Z, n < m -> q < p -> n - p < m - q.
Proof.
intros n m p q H1 H2.
apply NZlt_trans with (m - p);
[now apply -> Zminus_lt_mono_r | now apply -> Zminus_lt_mono_l].
Qed.

Theorem Zminus_le_mono_l : forall n m p : Z, n <= m <-> p - m <= p - n.
Proof.
intros n m p; do 2 rewrite <- Zadd_opp_r; rewrite <- Zadd_le_mono_l;
apply Zopp_le_mono.
Qed.

Theorem Zminus_le_mono_r : forall n m p : Z, n <= m <-> n - p <= m - p.
Proof.
intros n m p; do 2 rewrite <- Zadd_opp_r; apply Zadd_le_mono_r.
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
intros n m p q H1 H2. apply (Zle_lt_add_lt (- m) (- n));
[now apply -> Zopp_le_mono | now do 2 rewrite Zadd_opp_r].
Qed.

Theorem Zlt_le_minus_lt : forall n m p q : Z, n < m -> p - n <= q - m -> p < q.
Proof.
intros n m p q H1 H2. apply (Zlt_le_add_lt (- m) (- n));
[now apply -> Zopp_lt_mono | now do 2 rewrite Zadd_opp_r].
Qed.

Theorem Zle_le_minus_lt : forall n m p q : Z, n <= m -> p - n <= q - m -> p <= q.
Proof.
intros n m p q H1 H2. apply (Zle_le_add_le (- m) (- n));
[now apply -> Zopp_le_mono | now do 2 rewrite Zadd_opp_r].
Qed.

Theorem Zlt_add_lt_minus_r : forall n m p : Z, n + p < m <-> n < m - p.
Proof.
intros n m p. stepl (n + p - p < m - p) by symmetry; apply Zminus_lt_mono_r.
now rewrite Zadd_simpl_r.
Qed.

Theorem Zle_add_le_minus_r : forall n m p : Z, n + p <= m <-> n <= m - p.
Proof.
intros n m p. stepl (n + p - p <= m - p) by symmetry; apply Zminus_le_mono_r.
now rewrite Zadd_simpl_r.
Qed.

Theorem Zlt_add_lt_minus_l : forall n m p : Z, n + p < m <-> p < m - n.
Proof.
intros n m p. rewrite Zadd_comm; apply Zlt_add_lt_minus_r.
Qed.

Theorem Zle_add_le_minus_l : forall n m p : Z, n + p <= m <-> p <= m - n.
Proof.
intros n m p. rewrite Zadd_comm; apply Zle_add_le_minus_r.
Qed.

Theorem Zlt_minus_lt_add_r : forall n m p : Z, n - p < m <-> n < m + p.
Proof.
intros n m p. stepl (n - p + p < m + p) by symmetry; apply Zadd_lt_mono_r.
now rewrite Zminus_simpl_r.
Qed.

Theorem Zle_minus_le_add_r : forall n m p : Z, n - p <= m <-> n <= m + p.
Proof.
intros n m p. stepl (n - p + p <= m + p) by symmetry; apply Zadd_le_mono_r.
now rewrite Zminus_simpl_r.
Qed.

Theorem Zlt_minus_lt_add_l : forall n m p : Z, n - m < p <-> n < m + p.
Proof.
intros n m p. rewrite Zadd_comm; apply Zlt_minus_lt_add_r.
Qed.

Theorem Zle_minus_le_add_l : forall n m p : Z, n - m <= p <-> n <= m + p.
Proof.
intros n m p. rewrite Zadd_comm; apply Zle_minus_le_add_r.
Qed.

Theorem Zlt_minus_lt_add : forall n m p q : Z, n - m < p - q <-> n + q < m + p.
Proof.
intros n m p q. rewrite Zlt_minus_lt_add_l. rewrite Zadd_minus_assoc.
now rewrite <- Zlt_add_lt_minus_r.
Qed.

Theorem Zle_minus_le_add : forall n m p q : Z, n - m <= p - q <-> n + q <= m + p.
Proof.
intros n m p q. rewrite Zle_minus_le_add_l. rewrite Zadd_minus_assoc.
now rewrite <- Zle_add_le_minus_r.
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
intros n m p q H. rewrite Zlt_minus_lt_add in H. now apply Zadd_lt_cases.
Qed.

Theorem Zminus_le_cases : forall n m p q : Z, n - m <= p - q -> n <= m \/ q <= p.
Proof.
intros n m p q H. rewrite Zle_minus_le_add in H. now apply Zadd_le_cases.
Qed.

Theorem Zminus_neg_cases : forall n m : Z, n - m < 0 -> n < 0 \/ 0 < m.
Proof.
intros n m H; rewrite <- Zadd_opp_r in H.
setoid_replace (0 < m) with (- m < 0) using relation iff by (symmetry; apply Zopp_neg_pos).
now apply Zadd_neg_cases.
Qed.

Theorem Zminus_pos_cases : forall n m : Z, 0 < n - m -> 0 < n \/ m < 0.
Proof.
intros n m H; rewrite <- Zadd_opp_r in H.
setoid_replace (m < 0) with (0 < - m) using relation iff by (symmetry; apply Zopp_pos_neg).
now apply Zadd_pos_cases.
Qed.

Theorem Zminus_nonpos_cases : forall n m : Z, n - m <= 0 -> n <= 0 \/ 0 <= m.
Proof.
intros n m H; rewrite <- Zadd_opp_r in H.
setoid_replace (0 <= m) with (- m <= 0) using relation iff by (symmetry; apply Zopp_nonpos_nonneg).
now apply Zadd_nonpos_cases.
Qed.

Theorem Zminus_nonneg_cases : forall n m : Z, 0 <= n - m -> 0 <= n \/ m <= 0.
Proof.
intros n m H; rewrite <- Zadd_opp_r in H.
setoid_replace (m <= 0) with (0 <= - m) using relation iff by (symmetry; apply Zopp_nonneg_nonpos).
now apply Zadd_nonneg_cases.
Qed.

Section PosNeg.

Variable P : Z -> Prop.
Hypothesis P_wd : predicate_wd Zeq P.

Add Morphism P with signature Zeq ==> iff as P_morph. Proof. exact P_wd. Qed.

Theorem Z0_pos_neg :
  P 0 -> (forall n : Z, 0 < n -> P n /\ P (- n)) -> forall n : Z, P n.
Proof.
intros H1 H2 n. destruct (Zlt_trichotomy n 0) as [H3 | [H3 | H3]].
apply <- Zopp_pos_neg in H3. apply H2 in H3. destruct H3 as [_ H3].
now rewrite Zopp_involutive in H3.
now rewrite H3.
apply H2 in H3; now destruct H3.
Qed.

End PosNeg.

Ltac Z0_pos_neg n := induction_maker n ltac:(apply Z0_pos_neg).

End ZPlusOrderPropFunct.


