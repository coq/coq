(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Definition zerop : forall n, {n = 0} + {0 < n}.
destruct n; auto with arith.
Defined.

Definition lt_eq_lt_dec : forall n m, {n < m} + {n = m} + {m < n}.
Proof.
induction n; simple destruct m; auto with arith.
intros m0; elim (IHn m0); auto with arith.
induction 1; auto with arith.
Defined.

Lemma gt_eq_gt_dec : forall n m, {m > n} + {n = m} + {n > m}.
Proof lt_eq_lt_dec.

Lemma le_lt_dec : forall n m, {n <= m} + {m < n}.
Proof.
induction n.
auto with arith.
induction m.
auto with arith.
elim (IHn m); auto with arith.
Defined.

Definition le_le_S_dec : forall n m, {n <= m} + {S m <= n}.
Proof.
exact le_lt_dec.
Defined.

Definition le_ge_dec : forall n m, {n <= m} + {n >= m}.
Proof.
intros; elim (le_lt_dec n m); auto with arith.
Defined.

Definition le_gt_dec : forall n m, {n <= m} + {n > m}.
Proof.
exact le_lt_dec.
Defined.

Definition le_lt_eq_dec : forall n m, n <= m -> {n < m} + {n = m}.
Proof.
intros; elim (lt_eq_lt_dec n m); auto with arith.
intros; absurd (m < n); auto with arith.
Defined.

(** Proofs of decidability *)

Theorem dec_le : forall n m, decidable (n <= m).
intros x y; unfold decidable in |- *; elim (le_gt_dec x y);
 [ auto with arith | intro; right; apply gt_not_le; assumption ].
Qed.

Theorem dec_lt : forall n m, decidable (n < m).
intros x y; unfold lt in |- *; apply dec_le.
Qed.

Theorem dec_gt : forall n m, decidable (n > m).
intros x y; unfold gt in |- *; apply dec_lt.
Qed.

Theorem dec_ge : forall n m, decidable (n >= m).
intros x y; unfold ge in |- *; apply dec_le.
Qed.

Theorem not_eq : forall n m, n <> m -> n < m \/ m < n.
intros x y H; elim (lt_eq_lt_dec x y);
 [ intros H1; elim H1;
    [ auto with arith | intros H2; absurd (x = y); assumption ]
 | auto with arith ].
Qed.


Theorem not_le : forall n m, ~ n <= m -> n > m.
intros x y H; elim (le_gt_dec x y);
 [ intros H1; absurd (x <= y); assumption | trivial with arith ].
Qed.

Theorem not_gt : forall n m, ~ n > m -> n <= m.
intros x y H; elim (le_gt_dec x y);
 [ trivial with arith | intros H1; absurd (x > y); assumption ].
Qed.

Theorem not_ge : forall n m, ~ n >= m -> n < m.
intros x y H; exact (not_le y x H).
Qed.

Theorem not_lt : forall n m, ~ n < m -> n >= m.
intros x y H; exact (not_gt y x H). 
Qed.
