(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of addition.

 This file is mostly OBSOLETE now, see module [PeanoNat.Nat] instead.

 [Nat.add] is defined in [Init/Nat.v] as:
<<
Fixpoint add (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.
>>
*)

Require Import PeanoNat.

Local Open Scope nat_scope.

(** * Neutrality of 0, commutativity, associativity *)

Notation plus_0_l := Nat.add_0_l (only parsing).
Notation plus_0_r := Nat.add_0_r (only parsing).
Notation plus_comm := Nat.add_comm (only parsing).
Notation plus_assoc := Nat.add_assoc (only parsing).

Notation plus_permute := Nat.add_shuffle3 (only parsing).

Definition plus_Snm_nSm : forall n m, S n + m = n + S m :=
 Peano.plus_n_Sm.

Lemma plus_assoc_reverse n m p : n + m + p = n + (m + p).
Proof.
  symmetry. apply Nat.add_assoc.
Qed.

(** * Simplification *)

Lemma plus_reg_l n m p : p + n = p + m -> n = m.
Proof.
 apply Nat.add_cancel_l.
Qed.

Lemma plus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof.
 apply Nat.add_le_mono_l.
Qed.

Lemma plus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof.
 apply Nat.add_lt_mono_l.
Qed.

(** * Compatibility with order *)

Lemma plus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof.
 apply Nat.add_le_mono_l.
Qed.

Lemma plus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof.
 apply Nat.add_le_mono_r.
Qed.

Lemma plus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof.
 apply Nat.add_lt_mono_l.
Qed.

Lemma plus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof.
 apply Nat.add_lt_mono_r.
Qed.

Lemma plus_le_compat n m p q : n <= m -> p <= q -> n + p <= m + q.
Proof.
 apply Nat.add_le_mono.
Qed.

Lemma plus_le_lt_compat n m p q : n <= m -> p < q -> n + p < m + q.
Proof.
 apply Nat.add_le_lt_mono.
Qed.

Lemma plus_lt_le_compat n m p q : n < m -> p <= q -> n + p < m + q.
Proof.
 apply Nat.add_lt_le_mono.
Qed.

Lemma plus_lt_compat n m p q : n < m -> p < q -> n + p < m + q.
Proof.
 apply Nat.add_lt_mono.
Qed.

Lemma le_plus_l n m : n <= n + m.
Proof.
 apply Nat.le_add_r.
Qed.

Lemma le_plus_r n m : m <= n + m.
Proof.
 rewrite Nat.add_comm. apply Nat.le_add_r.
Qed.

Theorem le_plus_trans n m p : n <= m -> n <= m + p.
Proof.
  intros. now rewrite <- Nat.le_add_r.
Qed.

Theorem lt_plus_trans n m p : n < m -> n < m + p.
Proof.
  intros. apply Nat.lt_le_trans with m. trivial. apply Nat.le_add_r.
Qed.

(** * Inversion lemmas *)

Lemma plus_is_O n m : n + m = 0 -> n = 0 /\ m = 0.
Proof.
  destruct n; now split.
Qed.

Definition plus_is_one m n :
  m + n = 1 -> {m = 0 /\ n = 1} + {m = 1 /\ n = 0}.
Proof.
  destruct m as [| m]; auto.
  destruct m; auto.
  discriminate.
Defined.

(** * Derived properties *)

Notation plus_permute_2_in_4 := Nat.add_shuffle1 (only parsing).

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
Proof.
induction n as [| n IHn]; simpl; auto.
intro m; rewrite <- IHn; simpl; auto.
Qed.

(** * Discrimination *)

Lemma succ_plus_discr n m : n <> S (m+n).
Proof.
 apply Nat.succ_add_discr.
Qed.

Lemma n_SSn n : n <> S (S n).
Proof (succ_plus_discr n 1).

Lemma n_SSSn n : n <> S (S (S n)).
Proof (succ_plus_discr n 2).

Lemma n_SSSSn n : n <> S (S (S (S n))).
Proof (succ_plus_discr n 3).


(** * Compatibility Hints *)

Hint Immediate plus_comm : arith.
Hint Resolve plus_assoc plus_assoc_reverse : arith.
Hint Resolve plus_le_compat_l plus_le_compat_r : arith.
Hint Resolve le_plus_l le_plus_r le_plus_trans : arith.
Hint Immediate lt_plus_trans : arith.
Hint Resolve plus_lt_compat_l plus_lt_compat_r : arith.

(** For compatibility, we "Require" the same files as before *)

Require Import Le Lt.
