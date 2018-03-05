(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NZAxioms NZBase NZMul NZOrder.

Module Type NZAddOrderProp (Import NZ : NZOrdAxiomsSig').
Include NZBaseProp NZ <+ NZMulProp NZ <+ NZOrderProp NZ.

Theorem add_lt_mono_l : forall n m p, n < m <-> p + n < p + m.
Proof.
intros n m p; nzinduct p. now nzsimpl.
intro p. nzsimpl. now rewrite <- succ_lt_mono.
Qed.

Theorem add_lt_mono_r : forall n m p, n < m <-> n + p < m + p.
Proof.
intros n m p. rewrite (add_comm n p), (add_comm m p); apply add_lt_mono_l.
Qed.

Theorem add_lt_mono : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_trans with (m + p);
[now apply add_lt_mono_r | now apply add_lt_mono_l].
Qed.

Theorem add_le_mono_l : forall n m p, n <= m <-> p + n <= p + m.
Proof.
intros n m p; nzinduct p. now nzsimpl.
intro p. nzsimpl. now rewrite <- succ_le_mono.
Qed.

Theorem add_le_mono_r : forall n m p, n <= m <-> n + p <= m + p.
Proof.
intros n m p. rewrite (add_comm n p), (add_comm m p); apply add_le_mono_l.
Qed.

Theorem add_le_mono : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply le_trans with (m + p);
[now apply add_le_mono_r | now apply add_le_mono_l].
Qed.

Theorem add_lt_le_mono : forall n m p q, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply lt_le_trans with (m + p);
[now apply add_lt_mono_r | now apply add_le_mono_l].
Qed.

Theorem add_le_lt_mono : forall n m p q, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply le_lt_trans with (m + p);
[now apply add_le_mono_r | now apply add_lt_mono_l].
Qed.

Theorem add_pos_pos : forall n m, 0 < n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_mono.
Qed.

Theorem add_pos_nonneg : forall n m, 0 < n -> 0 <= m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_lt_le_mono.
Qed.

Theorem add_nonneg_pos : forall n m, 0 <= n -> 0 < m -> 0 < n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_lt_mono.
Qed.

Theorem add_nonneg_nonneg : forall n m, 0 <= n -> 0 <= m -> 0 <= n + m.
Proof.
intros n m H1 H2. rewrite <- (add_0_l 0). now apply add_le_mono.
Qed.

Theorem lt_add_pos_l : forall n m, 0 < n -> m < n + m.
Proof.
intros n m. rewrite (add_lt_mono_r 0 n m). now nzsimpl.
Qed.

Theorem lt_add_pos_r : forall n m, 0 < n -> m < m + n.
Proof.
intros; rewrite add_comm; now apply lt_add_pos_l.
Qed.

Theorem le_lt_add_lt : forall n m p q, n <= m -> p + m < q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases q p); [| assumption].
contradict H2. rewrite nlt_ge. now apply add_le_mono.
Qed.

Theorem lt_le_add_lt : forall n m p q, n < m -> p + m <= q + n -> p < q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases q p); [| assumption].
contradict H2. rewrite nle_gt. now apply add_le_lt_mono.
Qed.

Theorem le_le_add_le : forall n m p q, n <= m -> p + m <= q + n -> p <= q.
Proof.
intros n m p q H1 H2. destruct (le_gt_cases p q); [assumption |].
contradict H2. rewrite nle_gt. now apply add_lt_le_mono.
Qed.

Theorem add_lt_cases : forall n m p q, n + m < p + q -> n < p \/ m < q.
Proof.
intros n m p q H;
destruct (le_gt_cases p n) as [H1 | H1]; [| now left].
destruct (le_gt_cases q m) as [H2 | H2]; [| now right].
contradict H; rewrite nlt_ge. now apply add_le_mono.
Qed.

Theorem add_le_cases : forall n m p q, n + m <= p + q -> n <= p \/ m <= q.
Proof.
intros n m p q H.
destruct (le_gt_cases n p) as [H1 | H1]. now left.
destruct (le_gt_cases m q) as [H2 | H2]. now right.
contradict H; rewrite nle_gt. now apply add_lt_mono.
Qed.

Theorem add_neg_cases : forall n m, n + m < 0 -> n < 0 \/ m < 0.
Proof.
intros n m H; apply add_lt_cases; now nzsimpl.
Qed.

Theorem add_pos_cases : forall n m, 0 < n + m -> 0 < n \/ 0 < m.
Proof.
intros n m H; apply add_lt_cases; now nzsimpl.
Qed.

Theorem add_nonpos_cases : forall n m, n + m <= 0 -> n <= 0 \/ m <= 0.
Proof.
intros n m H; apply add_le_cases; now nzsimpl.
Qed.

Theorem add_nonneg_cases : forall n m, 0 <= n + m -> 0 <= n \/ 0 <= m.
Proof.
intros n m H; apply add_le_cases; now nzsimpl.
Qed.

(** Substraction *)

(** We can prove the existence of a subtraction of any number by
    a smaller one *)

Lemma le_exists_sub : forall n m, n<=m -> exists p, m == p+n /\ 0<=p.
Proof.
 intros n m H. apply le_ind with (4:=H). solve_proper.
 exists 0; nzsimpl; split; order.
 clear m H. intros m H (p & EQ & LE). exists (S p).
  split. nzsimpl. now f_equiv. now apply le_le_succ_r.
Qed.

(** For the moment, it doesn't seem possible to relate
    this existing subtraction with [sub].
*)

End NZAddOrderProp.

