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

Section Ensembles_facts.
Variable U: Type.

Lemma Extension: (B, C: (Ensemble U)) B == C -> (Same_set U B C).
Proof.
Intros B C H'; Rewrite H'; Auto with sets.
Qed.

Lemma Noone_in_empty: (x: U) ~ (In U (Empty_set U) x).
Proof.
Red; NewDestruct 1.
Qed.
Hints Resolve Noone_in_empty.

Lemma Included_Empty: (A: (Ensemble U))(Included U (Empty_set U) A).
Proof.
Intro; Red.
Intros x H; Elim (Noone_in_empty x); Auto with sets.
Qed.
Hints Resolve Included_Empty.

Lemma Add_intro1:
  (A: (Ensemble U)) (x, y: U) (In U A y) -> (In U (Add U A x) y).
Proof.
Unfold 1 Add; Auto with sets.
Qed.
Hints Resolve Add_intro1.

Lemma Add_intro2: (A: (Ensemble U)) (x: U) (In U (Add U A x) x).
Proof.
Unfold 1 Add; Auto with sets.
Qed.
Hints Resolve Add_intro2.

Lemma Inhabited_add: (A: (Ensemble U)) (x: U) (Inhabited U (Add U A x)).
Proof.
Intros A x.
Apply Inhabited_intro with x := x; Auto with sets.
Qed.
Hints Resolve Inhabited_add.

Lemma Inhabited_not_empty:
  (X: (Ensemble U)) (Inhabited U X) -> ~ X == (Empty_set U).
Proof.
Intros X H'; Elim H'.
Intros x H'0; Red; Intro H'1.
Absurd (In U X x); Auto with sets.
Rewrite H'1; Auto with sets.
Qed.
Hints Resolve Inhabited_not_empty.

Lemma Add_not_Empty :
 (A: (Ensemble U)) (x: U) ~ (Add U A x) == (Empty_set U).
Proof.
Auto with sets.
Qed.
Hints Resolve Add_not_Empty.

Lemma not_Empty_Add :
 (A: (Ensemble U)) (x: U) ~ (Empty_set U) == (Add U A x).
Proof.
Intros; Red; Intro H; Generalize (Add_not_Empty A x); Auto with sets.
Qed.
Hints Resolve not_Empty_Add.

Lemma Singleton_inv: (x, y: U) (In U (Singleton U x) y) -> x == y.
Proof.
Intros x y H'; Elim H'; Trivial with sets.
Qed.
Hints Resolve Singleton_inv.

Lemma Singleton_intro: (x, y: U) x == y -> (In U (Singleton U x) y).
Proof.
Intros x y H'; Rewrite H'; Trivial with sets.
Qed.
Hints Resolve Singleton_intro.

Lemma Union_inv:  (B, C: (Ensemble U)) (x: U) 
  (In U (Union U B C) x) -> (In U B x) \/ (In U C x).
Proof.
Intros B C x H'; Elim H'; Auto with sets.
Qed.

Lemma Add_inv:
  (A: (Ensemble U)) (x, y: U) (In U (Add U A x) y) -> (In U A y) \/ x == y.
Proof.
Intros A x y H'; Elim H'; Auto with sets.
Qed.

Lemma Intersection_inv:
  (B, C: (Ensemble U)) (x: U) (In U (Intersection U B C) x) ->
   (In U B x) /\ (In U C x).
Proof.
Intros B C x H'; Elim H'; Auto with sets.
Qed.
Hints Resolve Intersection_inv.

Lemma Couple_inv: (x, y, z: U) (In U (Couple U x y) z) -> z == x \/ z == y.
Proof.
Intros x y z H'; Elim H'; Auto with sets.
Qed.
Hints Resolve Couple_inv.

Lemma Setminus_intro:
  (A, B: (Ensemble U)) (x: U) (In U A x) -> ~ (In U B x) ->
   (In U (Setminus U A B) x).
Proof.
Unfold 1 Setminus; Red; Auto with sets.
Qed.
Hints Resolve Setminus_intro.
 
Lemma Strict_Included_intro:
  (X, Y: (Ensemble U)) (Included U X Y) /\ ~ X == Y -> 
                       (Strict_Included U X Y).
Proof.
Auto with sets.
Qed.
Hints Resolve Strict_Included_intro.

Lemma Strict_Included_strict: (X: (Ensemble U)) ~ (Strict_Included U X X).
Proof.
Intro X; Red; Intro H'; Elim H'.
Intros H'0 H'1; Elim H'1; Auto with sets.
Qed.
Hints Resolve Strict_Included_strict.

End Ensembles_facts.

Hints Resolve Singleton_inv Singleton_intro Add_intro1 Add_intro2 
	Intersection_inv Couple_inv Setminus_intro Strict_Included_intro
	Strict_Included_strict Noone_in_empty Inhabited_not_empty
	Add_not_Empty  not_Empty_Add Inhabited_add Included_Empty : sets v62.
