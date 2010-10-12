(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Properties of addition. [add] is defined in [Init/Peano.v] as:
<<
Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (plus n m) : nat_scope.
>>
 *)

Require Import Le.
Require Import Lt.

Open Local Scope nat_scope.

Implicit Types m n p q : nat.

(** * Zero is neutral *)

Lemma plus_0_l : forall n, 0 + n = n.
Proof.
  reflexivity.
Qed.

Lemma plus_0_r : forall n, n + 0 = n.
Proof.
  intro; symmetry  in |- *; apply plus_n_O.
Qed.

(** * Commutativity *)

Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m; elim n; simpl in |- *; auto with arith.
  intros y H; elim (plus_n_Sm m y); auto with arith.
Qed.
Hint Immediate plus_comm: arith v62.

(** * Associativity *)

Lemma plus_Snm_nSm : forall n m, S n + m = n + S m.
Proof.
  intros.
  simpl in |- *.
  rewrite (plus_comm n m).
  rewrite (plus_comm n (S m)).
  trivial with arith.
Qed.

Lemma plus_assoc : forall n m p, n + (m + p) = n + m + p.
Proof.
  intros n m p; elim n; simpl in |- *; auto with arith.
Qed.
Hint Resolve plus_assoc: arith v62.

Lemma plus_permute : forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros; rewrite (plus_assoc m n p); rewrite (plus_comm m n); auto with arith.
Qed.

Lemma plus_assoc_reverse : forall n m p, n + m + p = n + (m + p).
Proof.
  auto with arith.
Qed.
Hint Resolve plus_assoc_reverse: arith v62.

(** * Simplification *)

Lemma plus_reg_l : forall n m p, p + n = p + m -> n = m.
Proof.
  intros m p n; induction n; simpl in |- *; auto with arith.
Qed.

Lemma plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  induction p; simpl in |- *; auto with arith.
Qed.

Lemma plus_lt_reg_l : forall n m p, p + n < p + m -> n < m.
Proof.
  induction p; simpl in |- *; auto with arith.
Qed.

(** * Compatibility with order *)

Lemma plus_le_compat_l : forall n m p, n <= m -> p + n <= p + m.
Proof.
  induction p; simpl in |- *; auto with arith.
Qed.
Hint Resolve plus_le_compat_l: arith v62.

Lemma plus_le_compat_r : forall n m p, n <= m -> n + p <= m + p.
Proof.
  induction 1; simpl in |- *; auto with arith.
Qed.
Hint Resolve plus_le_compat_r: arith v62.

Lemma le_plus_l : forall n m, n <= n + m.
Proof.
  induction n; simpl in |- *; auto with arith.
Qed.
Hint Resolve le_plus_l: arith v62.

Lemma le_plus_r : forall n m, m <= n + m.
Proof.
  intros n m; elim n; simpl in |- *; auto with arith.
Qed.
Hint Resolve le_plus_r: arith v62.

Theorem le_plus_trans : forall n m p, n <= m -> n <= m + p.
Proof.
  intros; apply le_trans with (m := m); auto with arith.
Qed.
Hint Resolve le_plus_trans: arith v62.

Theorem lt_plus_trans : forall n m p, n < m -> n < m + p.
Proof.
  intros; apply lt_le_trans with (m := m); auto with arith.
Qed.
Hint Immediate lt_plus_trans: arith v62.

Lemma plus_lt_compat_l : forall n m p, n < m -> p + n < p + m.
Proof.
  induction p; simpl in |- *; auto with arith.
Qed.
Hint Resolve plus_lt_compat_l: arith v62.

Lemma plus_lt_compat_r : forall n m p, n < m -> n + p < m + p.
Proof.
  intros n m p H; rewrite (plus_comm n p); rewrite (plus_comm m p).
  elim p; auto with arith.
Qed.
Hint Resolve plus_lt_compat_r: arith v62.

Lemma plus_le_compat : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q H H0.
  elim H; simpl in |- *; auto with arith.
Qed.

Lemma plus_le_lt_compat : forall n m p q, n <= m -> p < q -> n + p < m + q.
Proof.
  unfold lt in |- *. intros. change (S n + p <= m + q) in |- *. rewrite plus_Snm_nSm.
  apply plus_le_compat; assumption.
Qed.

Lemma plus_lt_le_compat : forall n m p q, n < m -> p <= q -> n + p < m + q.
Proof.
  unfold lt in |- *. intros. change (S n + p <= m + q) in |- *. apply plus_le_compat; assumption.
Qed.

Lemma plus_lt_compat : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
  intros. apply plus_lt_le_compat. assumption.
  apply lt_le_weak. assumption.
Qed.

(** * Inversion lemmas *)

Lemma plus_is_O : forall n m, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intro m; destruct m as [| n]; auto.
  intros. discriminate H.
Qed.

Definition plus_is_one :
  forall m n, m + n = 1 -> {m = 0 /\ n = 1} + {m = 1 /\ n = 0}.
Proof.
  intro m; destruct m as [| n]; auto.
  destruct n; auto.
  intros.
  simpl in H. discriminate H.
Defined.

(** * Derived properties *)

Lemma plus_permute_2_in_4 : forall n m p q, n + m + (p + q) = n + p + (m + q).
Proof.
  intros m n p q.
  rewrite <- (plus_assoc m n (p + q)). rewrite (plus_assoc n p q).
  rewrite (plus_comm n p). rewrite <- (plus_assoc p n q). apply plus_assoc.
Qed.

(** * Tail-recursive plus *)

(** [tail_plus] is an alternative definition for [plus] which is
    tail-recursive, whereas [plus] is not. This can be useful
    when extracting programs. *)

Fixpoint tail_plus n m : nat :=
  match n with
    | O => m
    | S n => tail_plus n (S m)
  end.

Lemma plus_tail_plus : forall n m, n + m = tail_plus n m.
induction n as [| n IHn]; simpl in |- *; auto.
intro m; rewrite <- IHn; simpl in |- *; auto.
Qed.

(** * Discrimination *)

Lemma succ_plus_discr : forall n m, n <> S (plus m n).
Proof.
  intros n m; induction n as [|n IHn].
  discriminate.
  intro H; apply IHn; apply eq_add_S; rewrite H; rewrite <- plus_n_Sm;
    reflexivity.
Qed.

Lemma n_SSn : forall n, n <> S (S n).
Proof.
  intro n; exact (succ_plus_discr n 1).
Qed.

Lemma n_SSSn : forall n, n <> S (S (S n)).
Proof.
  intro n; exact (succ_plus_discr n 2).
Qed.

Lemma n_SSSSn : forall n, n <> S (S (S (S n))).
Proof.
  intro n; exact (succ_plus_discr n 3).
Qed.
