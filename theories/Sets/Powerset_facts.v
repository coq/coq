(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

Require Export Ensembles.
Require Export Constructive_sets.
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.
Require Export Powerset.

Section Sets_as_an_algebra.
  Variable U : Type.

  Theorem Empty_set_zero : forall X:Ensemble U, Union U (Empty_set U) X = X.
  Proof.
    auto 6 with sets.
  Qed.

  Theorem Empty_set_zero_right : forall X:Ensemble U, Union U X (Empty_set U) = X.
  Proof.
    auto 6 with sets.
  Qed.

  Theorem Empty_set_zero' : forall x:U, Add U (Empty_set U) x = Singleton U x.
  Proof.
    unfold Add at 1; auto using Empty_set_zero with sets.
  Qed.

  Lemma less_than_empty :
    forall X:Ensemble U, Included U X (Empty_set U) -> X = Empty_set U.
  Proof.
    auto with sets.
  Qed.

  Theorem Union_commutative : forall A B:Ensemble U, Union U A B = Union U B A.
  Proof.
    auto with sets.
  Qed.

  Theorem Union_associative :
    forall A B C:Ensemble U, Union U (Union U A B) C = Union U A (Union U B C).
  Proof.
    auto 9 with sets.
  Qed.

  Theorem Union_idempotent : forall A:Ensemble U, Union U A A = A.
  Proof.
    auto 7 with sets.
  Qed.

  Lemma Union_absorbs :
    forall A B:Ensemble U, Included U B A -> Union U A B = A.
  Proof.
    auto 7 with sets.
  Qed.

  Theorem Couple_as_union :
    forall x y:U, Union U (Singleton U x) (Singleton U y) = Couple U x y.
  Proof.
    intros x y; apply Extensionality_Ensembles; split; red.
    intros x0 H'; elim H'; (intros x1 H'0; elim H'0; auto with sets).
    intros x0 H'; elim H'; auto with sets.
  Qed.

  Theorem Triple_as_union :
    forall x y z:U,
      Union U (Union U (Singleton U x) (Singleton U y)) (Singleton U z) =
      Triple U x y z.
  Proof.
    intros x y z; apply Extensionality_Ensembles; split; red.
    intros x0 H'; elim H'.
    intros x1 H'0; elim H'0; (intros x2 H'1; elim H'1; auto with sets).
    intros x1 H'0; elim H'0; auto with sets.
    intros x0 H'; elim H'; auto with sets.
  Qed.

  Theorem Triple_as_Couple : forall x y:U, Couple U x y = Triple U x x y.
  Proof.
    intros x y.
    rewrite <- (Couple_as_union x y).
    rewrite <- (Union_idempotent (Singleton U x)).
    apply Triple_as_union.
  Qed.

  Theorem Triple_as_Couple_Singleton :
    forall x y z:U, Triple U x y z = Union U (Couple U x y) (Singleton U z).
  Proof.
    intros x y z.
    rewrite <- (Triple_as_union x y z).
    rewrite <- (Couple_as_union x y); auto with sets.
  Qed.

  Theorem Intersection_commutative :
    forall A B:Ensemble U, Intersection U A B = Intersection U B A.
  Proof.
    intros A B.
    apply Extensionality_Ensembles.
    split; red; intros x H'; elim H'; auto with sets.
  Qed.

  Theorem Distributivity :
    forall A B C:Ensemble U,
      Intersection U A (Union U B C) =
      Union U (Intersection U A B) (Intersection U A C).
  Proof.
    intros A B C.
    apply Extensionality_Ensembles.
    split; red; intros x H'.
    elim H'.
    intros x0 H'0 H'1; generalize H'0.
    elim H'1; auto with sets.
    elim H'; intros x0 H'0; elim H'0; auto with sets.
  Qed.

  Lemma Distributivity_l
       : forall (A B C : Ensemble U),
         Intersection U (Union U A B) C =
         Union U (Intersection U A C) (Intersection U B C).
  Proof.
     intros  A B C.
     rewrite Intersection_commutative.
     rewrite Distributivity.
     f_equal; apply Intersection_commutative.
  Qed.

  Theorem Distributivity' :
    forall A B C:Ensemble U,
      Union U A (Intersection U B C) =
      Intersection U (Union U A B) (Union U A C).
  Proof.
    intros A B C.
    apply Extensionality_Ensembles.
    split; red; intros x H'.
    elim H'; auto with sets.
    intros x0 H'0; elim H'0; auto with sets.
    elim H'.
    intros x0 H'0; elim H'0; auto with sets.
    intros x1 H'1 H'2; try exact H'2.
    generalize H'1.
    elim H'2; auto with sets.
  Qed.

  Theorem Union_add :
    forall (A B:Ensemble U) (x:U), Add U (Union U A B) x = Union U A (Add U B x).
  Proof.
    unfold Add; auto using Union_associative with sets.
  Qed.

  Theorem Non_disjoint_union :
    forall (X:Ensemble U) (x:U), In U X x -> Add U X x = X.
  Proof.
    intros X x H'; unfold Add.
    apply Extensionality_Ensembles; red.
    split; red; auto with sets.
    intros x0 H'0; elim H'0; auto with sets.
    intros t H'1; elim H'1; auto with sets.
  Qed.

  Theorem Non_disjoint_union' :
    forall (X:Ensemble U) (x:U), ~ In U X x -> Subtract U X x = X.
  Proof.
    intros X x H'; unfold Subtract.
    apply Extensionality_Ensembles.
    split; red; auto with sets.
    intros x0 H'0; elim H'0; auto with sets.
    intros x0 H'0; apply Setminus_intro; auto with sets.
    red; intro H'1; elim H'1.
    lapply (Singleton_inv U x x0); auto with sets.
    intro H'4; apply H'; rewrite H'4; auto with sets.
  Qed.

  Lemma singlx : forall x y:U, In U (Add U (Empty_set U) x) y -> x = y.
  Proof.
    intro x; rewrite (Empty_set_zero' x); auto with sets.
  Qed.

  Lemma incl_add :
    forall (A B:Ensemble U) (x:U),
      Included U A B -> Included U (Add U A x) (Add U B x).
  Proof.
    intros A B x H'; red; auto with sets.
    intros x0 H'0.
    lapply (Add_inv U A x x0); auto with sets.
    intro H'1; elim H'1;
      [ intro H'2; clear H'1 | intro H'2; rewrite <- H'2; clear H'1 ];
      auto with sets.
  Qed.

  Lemma incl_add_x :
    forall (A B:Ensemble U) (x:U),
      ~ In U A x -> Included U (Add U A x) (Add U B x) -> Included U A B.
  Proof.
    unfold Included.
    intros A B x H' H'0 x0 H'1.
    lapply (H'0 x0); auto with sets.
    intro H'2; lapply (Add_inv U B x x0); auto with sets.
    intro H'3; elim H'3;
      [ intro H'4; try exact H'4; clear H'3 | intro H'4; clear H'3 ].
    absurd (In U A x0); auto with sets.
    rewrite <- H'4; auto with sets.
  Qed.

  Lemma Add_commutative :
    forall (A:Ensemble U) (x y:U), Add U (Add U A x) y = Add U (Add U A y) x.
  Proof.
    intros A x y.
    unfold Add.
    rewrite (Union_associative A (Singleton U x) (Singleton U y)).
    rewrite (Union_commutative (Singleton U x) (Singleton U y)).
    rewrite <- (Union_associative A (Singleton U y) (Singleton U x));
      auto with sets.
  Qed.

  Lemma Add_commutative' :
    forall (A:Ensemble U) (x y z:U),
      Add U (Add U (Add U A x) y) z = Add U (Add U (Add U A z) x) y.
  Proof.
    intros A x y z.
    rewrite (Add_commutative (Add U A x) y z).
    rewrite (Add_commutative A x z); auto with sets.
  Qed.

  Lemma Add_distributes :
    forall (A B:Ensemble U) (x y:U),
      Included U B A -> Add U (Add U A x) y = Union U (Add U A x) (Add U B y).
  Proof.
    intros A B x y H'; try assumption.
    rewrite <- (Union_add (Add U A x) B y).
    unfold Add at 4.
    rewrite (Union_commutative A (Singleton U x)).
    rewrite Union_associative.
    rewrite (Union_absorbs A B H').
    rewrite (Union_commutative (Singleton U x) A).
    auto with sets.
  Qed.

  Lemma setcover_intro :
    forall (U:Type) (A x y:Ensemble U),
      Strict_Included U x y ->
      ~ (exists z : _, Strict_Included U x z /\ Strict_Included U z y) ->
      covers (Ensemble U) (Power_set_PO U A) y x.
  Proof.
    intros; apply Definition_of_covers; auto with sets.
  Qed.

  Lemma Disjoint_Intersection:
    forall A s1 s2, Disjoint A s1 s2 -> Intersection A s1 s2 = Empty_set A.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * destruct H.
      intros x H1. unfold In in *. exfalso. intuition. apply (H _ H1).
    * intuition.
  Qed.

  Lemma Intersection_Empty_set_l:
    forall A s, Intersection A (Empty_set A) s = Empty_set A.
  Proof.
    intros. auto with sets.
  Qed.

  Lemma Intersection_Empty_set_r:
    forall A s, Intersection A s (Empty_set A) = Empty_set A.
  Proof.
    intros. auto with sets.
  Qed.

  Lemma Seminus_Empty_set_l:
    forall A s, Setminus A (Empty_set A) s = Empty_set A.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * intros x H1. destruct H1. unfold In in *. assumption.
    * intuition.
  Qed.

  Lemma Seminus_Empty_set_r:
    forall A s, Setminus A s (Empty_set A) = s.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * intros x H1. destruct H1. unfold In in *. assumption.
    * intuition.
  Qed.

  Lemma Setminus_Union_l:
    forall A s1 s2 s3,
    Setminus A (Union A s1 s2) s3 = Union A (Setminus A s1 s3)  (Setminus A s2 s3).
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * intros x H. inversion H. inversion H0; intuition.
    * intros x H. constructor; inversion H; inversion H0; intuition.
  Qed.

  Lemma Setminus_Union_r:
    forall A s1 s2 s3,
    Setminus A s1 (Union A s2 s3) = Setminus A (Setminus A s1 s2) s3.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * intros x H. inversion H. constructor. intuition. contradict H1. intuition.
    * intros x H. inversion H. inversion H0. constructor; intuition. inversion H4; intuition.
  Qed.

 Lemma Setminus_Disjoint_noop:
    forall A s1 s2,
    Intersection A s1 s2 = Empty_set A -> Setminus A s1 s2 = s1.
  Proof.
    intros. apply Extensionality_Ensembles. split.
    * intros x H1. inversion_clear H1. intuition.
    * intros x H1. constructor; intuition. contradict H.
      apply Inhabited_not_empty.
      exists x. intuition.
  Qed.

  Lemma Setminus_Included_empty:
    forall A s1 s2,
    Included A s1 s2 -> Setminus A s1 s2 = Empty_set A.
  Proof.
    intros. apply Extensionality_Ensembles. split.
      * intros x H1. inversion_clear H1. contradiction H2. intuition.
      * intuition.
  Qed.

End Sets_as_an_algebra.

Hint Resolve Empty_set_zero Empty_set_zero' Union_associative Union_add
  singlx incl_add: sets.

