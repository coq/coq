(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* G. Huet 1-9-95 *)

Require Import Permut Setoid.
Require Plus. (* comm. and ass. of plus *)

Set Implicit Arguments.

Section multiset_defs.

  Variable A : Type.
  Variable eqA : A -> A -> Prop.
  Hypothesis eqA_equiv : Equivalence eqA.
  Hypothesis Aeq_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

  Inductive multiset : Type :=
    Bag : (A -> nat) -> multiset.

  Definition EmptyBag := Bag (fun a:A => 0).
  Definition SingletonBag (a:A) :=
    Bag (fun a':A => match Aeq_dec a a' with
                       | left _ => 1
                       | right _ => 0
                     end).

  Definition multiplicity (m:multiset) (a:A) : nat := let (f) := m in f a.

  (** multiset equality *)
  Definition meq (m1 m2:multiset) :=
    forall a:A, multiplicity m1 a = multiplicity m2 a.

  Lemma meq_refl : forall x:multiset, meq x x.
  Proof.
    destruct x; unfold meq; reflexivity.
  Qed.

  Lemma meq_trans : forall x y z:multiset, meq x y -> meq y z -> meq x z.
  Proof.
    unfold meq.
    destruct x; destruct y; destruct z.
    intros; rewrite H; auto.
  Qed.

  Lemma meq_sym : forall x y:multiset, meq x y -> meq y x.
  Proof.
    unfold meq.
    destruct x; destruct y; auto.
  Qed.

  (** multiset union *)
  Definition munion (m1 m2:multiset) :=
    Bag (fun a:A => multiplicity m1 a + multiplicity m2 a).

  Lemma munion_empty_left : forall x:multiset, meq x (munion EmptyBag x).
  Proof.
    unfold meq; unfold munion; simpl; auto.
  Qed.

  Lemma munion_empty_right : forall x:multiset, meq x (munion x EmptyBag).
  Proof.
    unfold meq; unfold munion; simpl; auto.
  Qed.

  Lemma munion_comm : forall x y:multiset, meq (munion x y) (munion y x).
  Proof.
    unfold meq; unfold multiplicity; unfold munion.
    destruct x; destruct y; auto with arith.
  Qed.

  Lemma munion_ass :
    forall x y z:multiset, meq (munion (munion x y) z) (munion x (munion y z)).
  Proof.
    unfold meq; unfold munion; unfold multiplicity.
    destruct x; destruct y; destruct z; auto with arith.
  Qed.

  Lemma meq_left :
    forall x y z:multiset, meq x y -> meq (munion x z) (munion y z).
  Proof.
    unfold meq; unfold munion; unfold multiplicity.
    destruct x; destruct y; destruct z.
    intros; elim H; auto with arith.
  Qed.

  Lemma meq_right :
    forall x y z:multiset, meq x y -> meq (munion z x) (munion z y).
  Proof.
    unfold meq; unfold munion; unfold multiplicity.
    destruct x; destruct y; destruct z.
    intros; elim H; auto.
  Qed.

  (** Here we should make multiset an abstract datatype, by hiding [Bag],
      [munion], [multiplicity]; all further properties are proved abstractly *)

  Lemma munion_rotate :
    forall x y z:multiset, meq (munion x (munion y z)) (munion z (munion x y)).
  Proof.
    intros; apply (op_rotate multiset munion meq).
      apply munion_comm.
      apply munion_ass.
      exact meq_trans.
      exact meq_sym.
      trivial.
  Qed.

  Lemma meq_congr :
    forall x y z t:multiset, meq x y -> meq z t -> meq (munion x z) (munion y t).
  Proof.
    intros; apply (cong_congr multiset munion meq); auto using meq_left, meq_right.
      exact meq_trans.
  Qed.

  Lemma munion_perm_left :
    forall x y z:multiset, meq (munion x (munion y z)) (munion y (munion x z)).
  Proof.
    intros; apply (perm_left multiset munion meq); auto using munion_comm, munion_ass, meq_left, meq_right, meq_sym.
      exact meq_trans.
  Qed.

  Lemma multiset_twist1 :
    forall x y z t:multiset,
      meq (munion x (munion (munion y z) t)) (munion (munion y (munion x t)) z).
  Proof.
    intros; apply (twist multiset munion meq); auto using munion_comm, munion_ass, meq_sym, meq_left, meq_right.
    exact meq_trans.
  Qed.

  Lemma multiset_twist2 :
    forall x y z t:multiset,
      meq (munion x (munion (munion y z) t)) (munion (munion y (munion x z)) t).
  Proof.
    intros; apply meq_trans with (munion (munion x (munion y z)) t).
    apply meq_sym; apply munion_ass.
    apply meq_left; apply munion_perm_left.
  Qed.

  (** specific for treesort *)

  Lemma treesort_twist1 :
    forall x y z t u:multiset,
      meq u (munion y z) ->
      meq (munion x (munion u t)) (munion (munion y (munion x t)) z).
  Proof.
    intros; apply meq_trans with (munion x (munion (munion y z) t)).
    apply meq_right; apply meq_left; trivial.
    apply multiset_twist1.
  Qed.

  Lemma treesort_twist2 :
    forall x y z t u:multiset,
      meq u (munion y z) ->
      meq (munion x (munion u t)) (munion (munion y (munion x z)) t).
  Proof.
    intros; apply meq_trans with (munion x (munion (munion y z) t)).
    apply meq_right; apply meq_left; trivial.
    apply multiset_twist2.
  Qed.

  (** SingletonBag *)

  Lemma meq_singleton : forall a a',
    eqA a a' -> meq (SingletonBag a) (SingletonBag a').
  Proof.
    intros; red; simpl; intro a0.
    destruct (Aeq_dec a a0) as [Ha|Ha]; rewrite H in Ha;
      decide (Aeq_dec a' a0) with Ha; reflexivity.
  Qed.

(*i theory of minter to do similarly
Require Min.
(* multiset intersection *)
Definition minter := [m1,m2:multiset]
    (Bag [a:A](min (multiplicity m1 a)(multiplicity m2 a))).
i*)

End multiset_defs.

Unset Implicit Arguments.

Hint Unfold meq multiplicity: datatypes.
Hint Resolve munion_empty_right munion_comm munion_ass meq_left meq_right
  munion_empty_left: datatypes.
Hint Immediate meq_sym: datatypes.
