(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Equality on natural numbers *)

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

(** * Propositional equality  *)

Fixpoint eq_nat n m : Prop :=
  match n, m with
    | O, O => True
    | O, S _ => False
    | S _, O => False
    | S n1, S m1 => eq_nat n1 m1
  end.

Theorem eq_nat_refl : forall n, eq_nat n n.
  induction n; simpl in |- *; auto.
Qed.
Hint Resolve eq_nat_refl: arith v62.

(** [eq] restricted to [nat] and [eq_nat] are equivalent *)

Lemma eq_eq_nat : forall n m, n = m -> eq_nat n m.
  induction 1; trivial with arith.
Qed.
Hint Immediate eq_eq_nat: arith v62.

Lemma eq_nat_eq : forall n m, eq_nat n m -> n = m.
  induction n; induction m; simpl in |- *; contradiction || auto with arith.
Qed.
Hint Immediate eq_nat_eq: arith v62.

Theorem eq_nat_is_eq : forall n m, eq_nat n m <-> n = m.
Proof.
  split; auto with arith.
Qed.

Theorem eq_nat_elim :
  forall n (P:nat -> Prop), P n -> forall m, eq_nat n m -> P m.
Proof.
  intros; replace m with n; auto with arith.
Qed.

Theorem eq_nat_decide : forall n m, {eq_nat n m} + {~ eq_nat n m}.
Proof.
  induction n.
  destruct m as [| n].
  auto with arith.
  intros; right; red in |- *; trivial with arith.
  destruct m as [| n0].
  right; red in |- *; auto with arith.
  intros.
  simpl in |- *.
  apply IHn.
Defined.


(** * Boolean equality on [nat] *)

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.

Definition beq_nat_eq : forall x y, true = beq_nat x y -> x = y.
Proof.
  double induction x y; simpl in |- *.
    reflexivity.
    intros n H1 H2. discriminate H2.
    intros n H1 H2. discriminate H2.
    intros n H1 z H2 H3. case (H2 _ H3). reflexivity.
Defined.

Lemma beq_nat_true : forall x y, beq_nat x y = true -> x=y.
Proof.
 induction x; destruct y; simpl; auto; intros; discriminate.
Qed.

Lemma beq_nat_false : forall x y, beq_nat x y = false -> x<>y.
Proof.
 induction x; destruct y; simpl; auto; intros; discriminate.
Qed.

Lemma beq_nat_true_iff : forall x y, beq_nat x y = true <-> x=y.
Proof.
 split. apply beq_nat_true.
 intros; subst; symmetry; apply beq_nat_refl.
Qed.

Lemma beq_nat_false_iff : forall x y, beq_nat x y = false <-> x<>y.
Proof.
 intros x y.
 split. apply beq_nat_false.
 generalize (beq_nat_true_iff x y).
 destruct beq_nat; auto.
 intros IFF NEQ. elim NEQ. apply IFF; auto.
Qed.
