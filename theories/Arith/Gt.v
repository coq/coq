(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Theorems about [gt] in [nat]. [gt] is defined in [Init/Peano.v] as:
<<
Definition gt (n m:nat) := m < n.
>>
*)

Require Import Le.
Require Import Lt.
Require Import Plus.
Open Local Scope nat_scope.

Implicit Types m n p : nat.

(** * Order and successor *)

Theorem gt_Sn_O : forall n, S n > 0.
Proof.
  auto with arith.
Qed.
Hint Resolve gt_Sn_O: arith v62.

Theorem gt_Sn_n : forall n, S n > n.
Proof.
  auto with arith.
Qed.
Hint Resolve gt_Sn_n: arith v62.

Theorem gt_n_S : forall n m, n > m -> S n > S m.
Proof.
  auto with arith.
Qed.
Hint Resolve gt_n_S: arith v62.

Lemma gt_S_n : forall n m, S m > S n -> m > n.
Proof.
  auto with arith.
Qed.
Hint Immediate gt_S_n: arith v62.

Theorem gt_S : forall n m, S n > m -> n > m \/ m = n.
Proof.
  intros n m H; unfold gt in |- *; apply le_lt_or_eq; auto with arith.
Qed.

Lemma gt_pred : forall n m, m > S n -> pred m > n.
Proof.
  auto with arith.
Qed.
Hint Immediate gt_pred: arith v62.

(** * Irreflexivity *)

Lemma gt_irrefl : forall n, ~ n > n.
Proof lt_irrefl.
Hint Resolve gt_irrefl: arith v62.

(** * Asymmetry *)

Lemma gt_asym : forall n m, n > m -> ~ m > n.
Proof fun n m => lt_asym m n.

Hint Resolve gt_asym: arith v62.

(** * Relating strict and large orders *)

Lemma le_not_gt : forall n m, n <= m -> ~ n > m.
Proof le_not_lt.
Hint Resolve le_not_gt: arith v62.

Lemma gt_not_le : forall n m, n > m -> ~ n <= m.
Proof.
auto with arith.
Qed.

Hint Resolve gt_not_le: arith v62.

Theorem le_S_gt : forall n m, S n <= m -> m > n.
Proof.
  auto with arith.
Qed.
Hint Immediate le_S_gt: arith v62.

Lemma gt_S_le : forall n m, S m > n -> n <= m.
Proof.
  intros n p; exact (lt_n_Sm_le n p).
Qed.
Hint Immediate gt_S_le: arith v62.

Lemma gt_le_S : forall n m, m > n -> S n <= m.
Proof.
  auto with arith.
Qed.
Hint Resolve gt_le_S: arith v62.

Lemma le_gt_S : forall n m, n <= m -> S m > n.
Proof.
  auto with arith.
Qed.
Hint Resolve le_gt_S: arith v62.

(** * Transitivity *)

Theorem le_gt_trans : forall n m p, m <= n -> m > p -> n > p.
Proof.
  red in |- *; intros; apply lt_le_trans with m; auto with arith.
Qed.

Theorem gt_le_trans : forall n m p, n > m -> p <= m -> n > p.
Proof.
  red in |- *; intros; apply le_lt_trans with m; auto with arith.
Qed.

Lemma gt_trans : forall n m p, n > m -> m > p -> n > p.
Proof.
  red in |- *; intros n m p H1 H2.
  apply lt_trans with m; auto with arith.
Qed.

Theorem gt_trans_S : forall n m p, S n > m -> m > p -> n > p.
Proof.
  red in |- *; intros; apply lt_le_trans with m; auto with arith.
Qed.

Hint Resolve gt_trans_S le_gt_trans gt_le_trans: arith v62.

(** * Comparison to 0 *)

Theorem gt_0_eq : forall n, n > 0 \/ 0 = n.
Proof.
  intro n; apply gt_S; auto with arith.
Qed.

(** * Simplification and compatibility *)

Lemma plus_gt_reg_l : forall n m p, p + n > p + m -> n > m.
Proof.
  red in |- *; intros n m p H; apply plus_lt_reg_l with p; auto with arith.
Qed.

Lemma plus_gt_compat_l : forall n m p, n > m -> p + n > p + m.
Proof.
  auto with arith.
Qed.
Hint Resolve plus_gt_compat_l: arith v62.

(* begin hide *)
Notation gt_O_eq := gt_0_eq (only parsing).
(* end hide *)
