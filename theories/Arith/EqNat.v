(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
Hint Resolve eq_nat_refl: arith v62.

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

Hint Immediate eq_eq_nat eq_nat_eq: arith v62.

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

Notation beq_nat := Nat.eqb (compat "8.4").

Notation beq_nat_true_iff := Nat.eqb_eq (compat "8.4").
Notation beq_nat_false_iff := Nat.eqb_neq (compat "8.4").

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
