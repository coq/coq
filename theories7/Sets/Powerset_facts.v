(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

(*i $Id$ i*)

Require Export Ensembles.
Require Export Constructive_sets.
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.
Require Export Powerset.

Section Sets_as_an_algebra.
Variable U: Type.
Hints Unfold not.

Theorem Empty_set_zero :
  (X: (Ensemble U)) (Union U (Empty_set U) X) == X.
Proof.
Auto 6 with sets.
Qed.
Hints Resolve Empty_set_zero.

Theorem Empty_set_zero' :
  (x: U) (Add U (Empty_set U) x) == (Singleton U x).
Proof.
Unfold 1 Add; Auto with sets.
Qed.
Hints Resolve Empty_set_zero'.

Lemma less_than_empty :
  (X: (Ensemble U)) (Included U X (Empty_set U)) -> X == (Empty_set U).
Proof.
Auto with sets.
Qed.
Hints Resolve less_than_empty.

Theorem Union_commutative :
  (A,B: (Ensemble U)) (Union U A B) == (Union U B A).
Proof.
Auto with sets.
Qed.

Theorem Union_associative :
  (A, B, C: (Ensemble U))
  (Union U (Union U A B) C) == (Union U A (Union U B C)).
Proof.
Auto 9 with sets.
Qed.
Hints Resolve Union_associative.

Theorem Union_idempotent : (A: (Ensemble U)) (Union U A A) == A.
Proof.
Auto 7 with sets.
Qed.

Lemma Union_absorbs :
  (A, B: (Ensemble U)) (Included U B A) -> (Union U A B) == A.
Proof.
Auto 7 with sets.
Qed.

Theorem Couple_as_union:
  (x, y: U) (Union U (Singleton U x) (Singleton U y)) == (Couple U x y).
Proof.
Intros x y; Apply Extensionality_Ensembles; Split; Red.
Intros x0 H'; Elim H'; (Intros x1 H'0; Elim H'0; Auto with sets).
Intros x0 H'; Elim H'; Auto with sets.
Qed.

Theorem Triple_as_union :
  (x, y, z: U)
  (Union U (Union U (Singleton U x) (Singleton U y)) (Singleton U z)) ==
  (Triple U x y z).
Proof.
Intros x y z; Apply Extensionality_Ensembles; Split; Red.
Intros x0 H'; Elim H'.
Intros x1 H'0; Elim H'0; (Intros x2 H'1; Elim H'1; Auto with sets).
Intros x1 H'0; Elim H'0; Auto with sets.
Intros x0 H'; Elim H'; Auto with sets.
Qed.

Theorem Triple_as_Couple : (x, y: U) (Couple U x y) == (Triple U x x y).
Proof.
Intros x y.
Rewrite <- (Couple_as_union x y).
Rewrite <- (Union_idempotent (Singleton U x)).
Apply Triple_as_union.
Qed.

Theorem Triple_as_Couple_Singleton :
  (x, y, z: U) (Triple U x y z) == (Union U (Couple U x y) (Singleton U z)).
Proof.
Intros x y z.
Rewrite <- (Triple_as_union x y z).
Rewrite <- (Couple_as_union x y); Auto with sets.
Qed.

Theorem Intersection_commutative :
  (A,B: (Ensemble U)) (Intersection U A B) == (Intersection U B A).
Proof.
Intros A B.
Apply Extensionality_Ensembles.
Split; Red; Intros x H'; Elim H'; Auto with sets.
Qed.

Theorem Distributivity :
  (A, B, C: (Ensemble U))
     (Intersection U A (Union U B C)) ==
     (Union U (Intersection U A B) (Intersection U A C)).
Proof.
Intros A B C.
Apply Extensionality_Ensembles.
Split; Red; Intros x H'.
Elim H'.
Intros x0 H'0 H'1; Generalize H'0.
Elim H'1; Auto with sets.
Elim H'; Intros x0 H'0; Elim H'0; Auto with sets.
Qed.

Theorem Distributivity' :
  (A, B, C: (Ensemble U))
     (Union U A (Intersection U B C)) ==
     (Intersection U (Union U A B) (Union U A C)).
Proof.
Intros A B C.
Apply Extensionality_Ensembles.
Split; Red; Intros x H'.
Elim H'; Auto with sets.
Intros x0 H'0; Elim H'0; Auto with sets.
Elim H'.
Intros x0 H'0; Elim H'0; Auto with sets.
Intros x1 H'1 H'2; Try Exact H'2.
Generalize H'1.
Elim H'2; Auto with sets.
Qed.

Theorem Union_add :
  (A, B: (Ensemble U)) (x: U)
    (Add U (Union U A B) x) == (Union U A (Add U B x)).
Proof.
Unfold Add; Auto with sets.
Qed.
Hints Resolve Union_add.

Theorem Non_disjoint_union :
  (X: (Ensemble U)) (x: U) (In U X x) -> (Add U X x) == X.
Intros X x H'; Unfold Add.
Apply Extensionality_Ensembles; Red.
Split; Red; Auto with sets.
Intros x0 H'0; Elim H'0; Auto with sets.
Intros t H'1; Elim H'1; Auto with sets.
Qed.

Theorem Non_disjoint_union' :
  (X: (Ensemble U)) (x: U) ~ (In U X x) -> (Subtract U X x) == X.
Proof.
Intros X x H'; Unfold Subtract.
Apply Extensionality_Ensembles.
Split; Red; Auto with sets.
Intros x0 H'0; Elim H'0; Auto with sets.
Intros x0 H'0; Apply Setminus_intro; Auto with sets.
Red; Intro H'1; Elim H'1.
LApply (Singleton_inv U x x0); Auto with sets.
Intro H'4; Apply H'; Rewrite H'4; Auto with sets.
Qed.

Lemma singlx : (x, y: U) (In U (Add U (Empty_set U) x) y) -> x == y.
Proof.
Intro x; Rewrite (Empty_set_zero' x); Auto with sets.
Qed.
Hints Resolve singlx.

Lemma incl_add :
  (A, B: (Ensemble U)) (x: U) (Included U A B) ->
   (Included U (Add U A x) (Add U B x)).
Proof.
Intros A B x H'; Red; Auto with sets.
Intros x0 H'0.
LApply (Add_inv U A x x0); Auto with sets.
Intro H'1; Elim H'1;
 [Intro H'2; Clear H'1 | Intro H'2; Rewrite <- H'2; Clear H'1]; Auto with sets.
Qed.
Hints Resolve incl_add.

Lemma incl_add_x :
  (A, B: (Ensemble U))
  (x: U) ~ (In U A x) -> (Included U (Add U A x) (Add U B x)) ->
   (Included U A B).
Proof.
Unfold Included.
Intros A B x H' H'0 x0 H'1.
LApply (H'0 x0); Auto with sets.
Intro H'2; LApply (Add_inv U B x x0); Auto with sets.
Intro H'3; Elim H'3;
 [Intro H'4; Try Exact H'4; Clear H'3 | Intro H'4; Clear H'3].
Absurd (In U A x0); Auto with sets.
Rewrite <- H'4; Auto with sets.
Qed.

Lemma Add_commutative :
  (A: (Ensemble U)) (x, y: U) (Add U (Add U A x) y) == (Add U (Add U A y) x).
Proof.
Intros A x y.
Unfold Add.
Rewrite (Union_associative A (Singleton U x) (Singleton U y)).
Rewrite (Union_commutative (Singleton U x) (Singleton U y)).
Rewrite <- (Union_associative A (Singleton U y) (Singleton U x)); Auto with sets.
Qed.

Lemma Add_commutative' :
  (A: (Ensemble U)) (x, y, z: U)
    (Add U (Add U (Add U A x) y) z) == (Add U (Add U (Add U A z) x) y).
Proof.
Intros A x y z.
Rewrite (Add_commutative (Add U A x) y z).
Rewrite (Add_commutative A x z); Auto with sets.
Qed.

Lemma Add_distributes :
  (A, B: (Ensemble U)) (x, y: U) (Included U B A) ->
  (Add U (Add U A x) y) == (Union U (Add U A x) (Add U B y)).
Proof.
Intros A B x y H'; Try Assumption.
Rewrite <- (Union_add (Add U A x) B y).
Unfold 4 Add.
Rewrite (Union_commutative A (Singleton U x)).
Rewrite Union_associative.
Rewrite (Union_absorbs A B H').
Rewrite (Union_commutative (Singleton U x) A).
Auto with sets.
Qed.

Lemma setcover_intro :
  (U: Type)
  (A: (Ensemble U))
  (x, y: (Ensemble U))
  (Strict_Included U x y) ->
  ~ (EXT z | (Strict_Included U x z) 
              /\ (Strict_Included U z y)) ->
   (covers (Ensemble U) (Power_set_PO U A) y x).
Proof.
Intros; Apply Definition_of_covers; Auto with sets.
Qed.
Hints Resolve setcover_intro.

End Sets_as_an_algebra.

Hints Resolve Empty_set_zero Empty_set_zero' Union_associative Union_add
	singlx incl_add : sets v62.


