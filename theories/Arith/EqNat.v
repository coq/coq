(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Local Open Scope nat_scope.

(** Equality on natural numbers *)

(** * Propositional equality  *)

Fixpoint eq_nat n m : Prop :=
  match n, m with
    | O, O => True
    | O, S _ => False
    | S _, O => False
    | S n1, S m1 => eq_nat n1 m1
  end.

Theorem eq_nat_refl n : eq_nat n n.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve eq_nat_refl: arith.

(** [eq] restricted to [nat] and [eq_nat] are equivalent *)

Theorem eq_nat_is_eq n m : eq_nat n m <-> n = m.
Proof.
  split.
  - revert m; induction n; destruct m; simpl; contradiction || auto.
  - intros <-; apply eq_nat_refl.
Qed.

Lemma eq_eq_nat n m : n = m -> eq_nat n m.
Proof.
 apply eq_nat_is_eq.
Qed.

Lemma eq_nat_eq n m : eq_nat n m -> n = m.
Proof.
 apply eq_nat_is_eq.
Qed.

Hint Immediate eq_eq_nat eq_nat_eq: arith.

Theorem eq_nat_elim :
  forall n (P:nat -> Prop), P n -> forall m, eq_nat n m -> P m.
Proof.
  intros; replace m with n; auto with arith.
Qed.

Theorem eq_nat_decide : forall n m, {eq_nat n m} + {~ eq_nat n m}.
Proof.
  induction n; destruct m; simpl.
  - left; trivial.
  - right; intro; trivial.
  - right; intro; trivial.
  - apply IHn.
Defined.


(** * Boolean equality on [nat].

   We reuse the one already defined in module [Nat].
   In scope [nat_scope], the notation "=?" can be used. *)

Notation beq_nat := Nat.eqb (only parsing).

Notation beq_nat_true_iff := Nat.eqb_eq (only parsing).
Notation beq_nat_false_iff := Nat.eqb_neq (only parsing).

Lemma beq_nat_refl n : true = (n =? n).
Proof.
 symmetry. apply Nat.eqb_refl.
Qed.

Lemma beq_nat_true n m : (n =? m) = true -> n=m.
Proof.
 apply Nat.eqb_eq.
Qed.

Lemma beq_nat_false n m : (n =? m) = false -> n<>m.
Proof.
 apply Nat.eqb_neq.
Qed.

(** TODO: is it really useful here to have a Defined ?
    Otherwise we could use Nat.eqb_eq *)

Definition beq_nat_eq : forall n m, true = (n =? m) -> n = m.
Proof.
  induction n; destruct m; simpl.
  - reflexivity.
  - discriminate.
  - discriminate.
  - intros H. case (IHn _ H). reflexivity.
Defined.
