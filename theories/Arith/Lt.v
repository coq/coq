(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Theorems about [lt] in nat. [lt] is defined in library [Init/Peano.v] as:
<<
Definition lt (n m:nat) := S n <= m.
Infix "<" := lt : nat_scope.
>>
*)

Require Import Le.
Open Local Scope nat_scope.

Implicit Types m n p : nat.

(** * Irreflexivity *)

Theorem lt_irrefl : forall n, ~ n < n.
Proof le_Sn_n.
Hint Resolve lt_irrefl: arith v62.

(** * Relationship between [le] and [lt] *)

Theorem lt_le_S : forall n m, n < m -> S n <= m.
Proof.
  auto with arith.
Qed.
Hint Immediate lt_le_S: arith v62.

Theorem lt_n_Sm_le : forall n m, n < S m -> n <= m.
Proof.
  auto with arith.
Qed.
Hint Immediate lt_n_Sm_le: arith v62.

Theorem le_lt_n_Sm : forall n m, n <= m -> n < S m.
Proof.
  auto with arith.
Qed.
Hint Immediate le_lt_n_Sm: arith v62.

Theorem le_not_lt : forall n m, n <= m -> ~ m < n.
Proof.
  induction 1; auto with arith.
Qed.

Theorem lt_not_le : forall n m, n < m -> ~ m <= n.
Proof.
  red in |- *; intros n m Lt Le; exact (le_not_lt m n Le Lt).
Qed.
Hint Immediate le_not_lt lt_not_le: arith v62.

(** * Asymmetry *)

Theorem lt_asym : forall n m, n < m -> ~ m < n.
Proof.
  induction 1; auto with arith.
Qed.

(** * Order and successor *)

Theorem lt_n_Sn : forall n, n < S n.
Proof.
  auto with arith.
Qed.
Hint Resolve lt_n_Sn: arith v62.

Theorem lt_S : forall n m, n < m -> n < S m.
Proof.
  auto with arith.
Qed.
Hint Resolve lt_S: arith v62.

Theorem lt_n_S : forall n m, n < m -> S n < S m.
Proof.
  auto with arith.
Qed.
Hint Resolve lt_n_S: arith v62.

Theorem lt_S_n : forall n m, S n < S m -> n < m.
Proof.
  auto with arith.
Qed.
Hint Immediate lt_S_n: arith v62.

Theorem lt_0_Sn : forall n, 0 < S n.
Proof.
  auto with arith.
Qed.
Hint Resolve lt_0_Sn: arith v62.

Theorem lt_n_O : forall n, ~ n < 0.
Proof le_Sn_O.
Hint Resolve lt_n_O: arith v62.

(** * Predecessor *)

Lemma S_pred : forall n m, m < n -> n = S (pred n).
Proof.
induction 1; auto with arith.
Qed.

Lemma lt_pred : forall n m, S n < m -> n < pred m.
Proof.
induction 1; simpl in |- *; auto with arith.
Qed.
Hint Immediate lt_pred: arith v62.

Lemma lt_pred_n_n : forall n, 0 < n -> pred n < n.
destruct 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve lt_pred_n_n: arith v62.

(** * Transitivity properties *)

Theorem lt_trans : forall n m p, n < m -> m < p -> n < p.
Proof.
  induction 2; auto with arith.
Qed.

Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof.
  induction 2; auto with arith.
Qed.

Theorem le_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof.
  induction 2; auto with arith.
Qed.

Hint Resolve lt_trans lt_le_trans le_lt_trans: arith v62.

(** * Large = strict or equal *)

Theorem le_lt_or_eq : forall n m, n <= m -> n < m \/ n = m.
Proof.
  induction 1; auto with arith.
Qed.

Theorem le_lt_or_eq_iff : forall n m, n <= m <-> n < m \/ n = m.
Proof.
  split.
  intros; apply le_lt_or_eq; auto.
  destruct 1; subst; auto with arith.
Qed.

Theorem lt_le_weak : forall n m, n < m -> n <= m.
Proof.
  auto with arith.
Qed.
Hint Immediate lt_le_weak: arith v62.

(** * Dichotomy *)

Theorem le_or_lt : forall n m, n <= m \/ m < n.
Proof.
  intros n m; pattern n, m in |- *; apply nat_double_ind; auto with arith.
  induction 1; auto with arith.
Qed.

Theorem nat_total_order : forall n m, n <> m -> n < m \/ m < n.
Proof.
  intros m n diff.
  elim (le_or_lt n m); [ intro H'0 | auto with arith ].
  elim (le_lt_or_eq n m); auto with arith.
  intro H'; elim diff; auto with arith.
Qed.

(** * Comparison to 0 *)

Theorem neq_0_lt : forall n, 0 <> n -> 0 < n.
Proof.
  induction n; auto with arith.
  intros; absurd (0 = 0); trivial with arith.
Qed.
Hint Immediate neq_0_lt: arith v62.

Theorem lt_0_neq : forall n, 0 < n -> 0 <> n.
Proof.
  induction 1; auto with arith.
Qed.
Hint Immediate lt_0_neq: arith v62.

(* begin hide *)
Notation lt_O_Sn := lt_0_Sn (only parsing).
Notation neq_O_lt := neq_0_lt (only parsing).
Notation lt_O_neq := lt_0_neq (only parsing).
(* end hide *)
