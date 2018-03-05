(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Properties of multiplication.

 This file is mostly OBSOLETE now, see module [PeanoNat.Nat] instead.

 [Nat.mul] is defined in [Init/Nat.v].
*)

Require Import PeanoNat.
(** For Compatibility: *)
Require Export Plus Minus Le Lt.

Local Open Scope nat_scope.

(** * [nat] is a semi-ring *)

(** ** Zero property *)

Notation mult_0_l := Nat.mul_0_l (only parsing). (* 0 * n = 0 *)
Notation mult_0_r := Nat.mul_0_r (only parsing). (* n * 0 = 0 *)

(** ** 1 is neutral *)

Notation mult_1_l := Nat.mul_1_l (only parsing). (* 1 * n = n *)
Notation mult_1_r := Nat.mul_1_r (only parsing). (* n * 1 = n *)

Hint Resolve mult_1_l mult_1_r: arith.

(** ** Commutativity *)

Notation mult_comm := Nat.mul_comm (only parsing). (* n * m = m * n *)

Hint Resolve mult_comm: arith.

(** ** Distributivity *)

Notation mult_plus_distr_r :=
  Nat.mul_add_distr_r (only parsing). (* (n+m)*p = n*p + m*p *)

Notation mult_plus_distr_l :=
  Nat.mul_add_distr_l (only parsing). (* n*(m+p) = n*m + n*p *)

Notation mult_minus_distr_r :=
  Nat.mul_sub_distr_r (only parsing). (* (n-m)*p = n*p - m*p *)

Notation mult_minus_distr_l :=
  Nat.mul_sub_distr_l (only parsing). (* n*(m-p) = n*m - n*p *)

Hint Resolve mult_plus_distr_r: arith.
Hint Resolve mult_minus_distr_r: arith.
Hint Resolve mult_minus_distr_l: arith.

(** ** Associativity *)

Notation mult_assoc := Nat.mul_assoc (only parsing). (* n*(m*p)=n*m*p *)

Lemma mult_assoc_reverse n m p : n * m * p = n * (m * p).
Proof.
 symmetry. apply Nat.mul_assoc.
Qed.

Hint Resolve mult_assoc_reverse: arith.
Hint Resolve mult_assoc: arith.

(** ** Inversion lemmas *)

Lemma mult_is_O n m : n * m = 0 -> n = 0 \/ m = 0.
Proof.
 apply Nat.eq_mul_0.
Qed.

Lemma mult_is_one n m : n * m = 1 -> n = 1 /\ m = 1.
Proof.
 apply Nat.eq_mul_1.
Qed.

(** ** Multiplication and successor *)

Notation mult_succ_l := Nat.mul_succ_l (only parsing). (* S n * m = n * m + m *)
Notation mult_succ_r := Nat.mul_succ_r (only parsing). (* n * S m = n * m + n *)

(** * Compatibility with orders *)

Lemma mult_O_le n m : m = 0 \/ n <= m * n.
Proof.
 destruct m; [left|right]; simpl; trivial using Nat.le_add_r.
Qed.
Hint Resolve mult_O_le: arith.

Lemma mult_le_compat_l n m p : n <= m -> p * n <= p * m.
Proof.
 apply Nat.mul_le_mono_nonneg_l, Nat.le_0_l. (* TODO : get rid of 0<=n hyp *)
Qed.
Hint Resolve mult_le_compat_l: arith.

Lemma mult_le_compat_r n m p : n <= m -> n * p <= m * p.
Proof.
 apply Nat.mul_le_mono_nonneg_r, Nat.le_0_l.
Qed.

Lemma mult_le_compat n m p q : n <= m -> p <= q -> n * p <= m * q.
Proof.
  intros. apply Nat.mul_le_mono_nonneg; trivial; apply Nat.le_0_l.
Qed.

Lemma mult_S_lt_compat_l n m p : m < p -> S n * m < S n * p.
Proof.
  apply Nat.mul_lt_mono_pos_l, Nat.lt_0_succ.
Qed.

Hint Resolve mult_S_lt_compat_l: arith.

Lemma mult_lt_compat_l n m p : n < m -> 0 < p -> p * n < p * m.
Proof.
 intros. now apply Nat.mul_lt_mono_pos_l.
Qed.

Lemma mult_lt_compat_r n m p : n < m -> 0 < p -> n * p < m * p.
Proof.
 intros. now apply Nat.mul_lt_mono_pos_r.
Qed.

Lemma mult_S_le_reg_l n m p : S n * m <= S n * p -> m <= p.
Proof.
 apply Nat.mul_le_mono_pos_l, Nat.lt_0_succ.
Qed.

(** * n|->2*n and n|->2n+1 have disjoint image *)

Theorem odd_even_lem p q : 2 * p + 1 <> 2 * q.
Proof.
 intro. apply (Nat.Even_Odd_False (2*q)).
 - now exists q.
 - now exists p.
Qed.


(** * Tail-recursive mult *)

(** [tail_mult] is an alternative definition for [mult] which is
    tail-recursive, whereas [mult] is not. This can be useful
    when extracting programs. *)

Fixpoint mult_acc (s:nat) m n : nat :=
  match n with
    | O => s
    | S p => mult_acc (tail_plus m s) m p
  end.

Lemma mult_acc_aux : forall n m p, m + n * p = mult_acc m p n.
Proof.
  induction n as [| n IHn]; simpl; auto.
  intros. rewrite Nat.add_assoc, IHn. f_equal.
  rewrite Nat.add_comm. apply plus_tail_plus.
Qed.

Definition tail_mult n m := mult_acc 0 m n.

Lemma mult_tail_mult : forall n m, n * m = tail_mult n m.
Proof.
  intros; unfold tail_mult; rewrite <- mult_acc_aux; auto.
Qed.

(** [TailSimpl] transforms any [tail_plus] and [tail_mult] into [plus]
    and [mult] and simplify *)

Ltac tail_simpl :=
  repeat rewrite <- plus_tail_plus; repeat rewrite <- mult_tail_mult;
    simpl.
