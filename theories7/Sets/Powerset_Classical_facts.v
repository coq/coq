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
Require Export Powerset_facts.
Require Export Classical_Type.
Require Export Classical_sets.

Section Sets_as_an_algebra.

Variable U: Type.

Lemma sincl_add_x:
  (A, B: (Ensemble U))
  (x: U) ~ (In U A x) -> (Strict_Included U (Add U A x) (Add U B x)) ->
                         (Strict_Included U A B).
Proof.
Intros A B x H' H'0; Red.
LApply (Strict_Included_inv U (Add U A x) (Add U B x)); Auto with sets.
Clear H'0; Intro H'0; Split.
Apply incl_add_x with x := x; Tauto.
Elim H'0; Intros H'1 H'2; Elim H'2; Clear H'0 H'2.
Intros x0 H'0.
Red; Intro H'2.
Elim H'0; Clear H'0.
Rewrite <- H'2; Auto with sets.
Qed.

Lemma incl_soustr_in:
  (X: (Ensemble U)) (x: U) (In U X x) -> (Included U (Subtract U X x) X).
Proof.
Intros X x H'; Red.
Intros x0 H'0; Elim H'0; Auto with sets.
Qed.
Hints Resolve incl_soustr_in : sets v62.

Lemma incl_soustr:
  (X, Y: (Ensemble U)) (x: U) (Included U X Y) ->
   (Included U (Subtract U X x) (Subtract U Y x)).
Proof.
Intros X Y x H'; Red.
Intros x0 H'0; Elim H'0.
Intros H'1 H'2.
Apply Subtract_intro; Auto with sets.
Qed.
Hints Resolve incl_soustr : sets v62.


Lemma incl_soustr_add_l:
  (X: (Ensemble U)) (x: U) (Included U (Subtract U (Add U X x) x) X).
Proof.
Intros X x; Red.
Intros x0 H'; Elim H'; Auto with sets.
Intro H'0; Elim H'0; Auto with sets.
Intros t H'1 H'2; Elim H'2; Auto with sets.
Qed.
Hints Resolve incl_soustr_add_l : sets v62.

Lemma incl_soustr_add_r:
  (X: (Ensemble U)) (x: U) ~ (In U X x) ->
   (Included U X (Subtract U (Add U X x) x)).
Proof.
Intros X x H'; Red.
Intros x0 H'0; Try Assumption.
Apply Subtract_intro; Auto with sets.
Red; Intro H'1; Apply H'; Rewrite H'1; Auto with sets.
Qed.
Hints Resolve incl_soustr_add_r : sets v62.

Lemma add_soustr_2:
  (X: (Ensemble U)) (x: U) (In U X x) ->
   (Included U X (Add U (Subtract U X x) x)).
Proof.
Intros X x H'; Red.
Intros x0 H'0; Try Assumption.
Elim (classic x == x0); Intro K; Auto with sets.
Elim K; Auto with sets.
Qed.

Lemma add_soustr_1:
  (X: (Ensemble U)) (x: U) (In U X x) ->
   (Included U (Add U (Subtract U X x) x) X).
Proof.
Intros X x H'; Red.
Intros x0 H'0; Elim H'0; Auto with sets.
Intros y H'1; Elim H'1; Auto with sets.
Intros t H'1; Try Assumption.
Rewrite <- (Singleton_inv U x t); Auto with sets.
Qed.
Hints Resolve add_soustr_1 add_soustr_2 : sets v62.

Lemma add_soustr_xy:
  (X: (Ensemble U)) (x, y: U) ~ x == y ->
    (Subtract U (Add U X x) y) == (Add U (Subtract U X y) x).
Proof.
Intros X x y H'; Apply Extensionality_Ensembles.
Split; Red.
Intros x0 H'0; Elim H'0; Auto with sets.
Intro H'1; Elim H'1.
Intros u H'2 H'3; Try Assumption.
Apply Add_intro1.
Apply Subtract_intro; Auto with sets.
Intros t H'2 H'3; Try Assumption.
Elim (Singleton_inv U x t); Auto with sets.
Intros u H'2; Try Assumption.
Elim (Add_inv U (Subtract U X y) x u); Auto with sets.
Intro H'0; Elim H'0; Auto with sets.
Intro H'0; Rewrite <- H'0; Auto with sets.
Qed.
Hints Resolve add_soustr_xy : sets v62.

Lemma incl_st_add_soustr:
  (X, Y: (Ensemble U)) (x: U) ~ (In U X x) -> 
   (Strict_Included U (Add U X x) Y) ->
   (Strict_Included U X (Subtract U Y x)).
Proof.
Intros X Y x H' H'0; Apply sincl_add_x with x := x; Auto with sets.
Split.
Elim H'0.
Intros H'1 H'2.
Generalize (Inclusion_is_transitive U).
Intro H'4; Red in H'4.
Apply H'4 with y := Y; Auto with sets.
Red in H'0.
Elim H'0; Intros H'1 H'2; Try Exact H'1; Clear H'0. (* PB *)
Red; Intro H'0; Apply H'2.
Rewrite H'0; Auto 8 with sets.
Qed.

Lemma Sub_Add_new:
  (X: (Ensemble U)) (x: U) ~ (In U X x) -> X == (Subtract U (Add U X x) x).
Proof.
Auto with sets.
Qed.

Lemma Simplify_add:
  (X, X0 : (Ensemble U)) (x: U)
  ~ (In U X x) -> ~ (In U X0 x) ->  (Add U X x) == (Add U X0 x) -> X == X0.
Proof.
Intros X X0 x H' H'0 H'1; Try Assumption.
Rewrite (Sub_Add_new X x); Auto with sets.
Rewrite (Sub_Add_new X0 x); Auto with sets.
Rewrite H'1; Auto with sets.
Qed.

Lemma Included_Add:
  (X, A: (Ensemble U)) (x: U) (Included U X (Add U A x)) ->
   (Included U X A) \/
   (EXT A' | X == (Add U A' x) /\ (Included U A' A)).
Proof.
Intros X A x H'0; Try Assumption.
Elim (classic (In U X x)).
Intro H'1; Right; Try Assumption.
Exists (Subtract U X x).
Split; Auto with sets.
Red in H'0.
Red.
Intros x0 H'2; Try Assumption.
LApply (Subtract_inv U X x x0); Auto with sets.
Intro H'3; Elim H'3; Intros K K'; Clear H'3.
LApply (H'0 x0); Auto with sets.
Intro H'3; Try Assumption.
LApply (Add_inv U A x x0); Auto with sets.
Intro H'4; Elim H'4;
 [Intro H'5; Try Exact H'5; Clear H'4 | Intro H'5; Clear H'4].
Elim K'; Auto with sets.
Intro H'1; Left; Try Assumption.
Red in H'0.
Red.
Intros x0 H'2; Try Assumption.
LApply (H'0 x0); Auto with sets.
Intro H'3; Try Assumption.
LApply (Add_inv U A x x0); Auto with sets.
Intro H'4; Elim H'4;
 [Intro H'5; Try Exact H'5; Clear H'4 | Intro H'5; Clear H'4].
Absurd (In U X x0); Auto with sets.
Rewrite <- H'5; Auto with sets.
Qed.

Lemma setcover_inv:
 (A: (Ensemble U))
 (x, y: (Ensemble U)) (covers (Ensemble U) (Power_set_PO U A) y x) ->
 (Strict_Included U x y) /\
 ((z: (Ensemble U)) (Included U x z) -> (Included U z y) -> x == z \/ z == y).
Proof.
Intros A x y H'; Elim H'.
Unfold Strict_Rel_of; Simpl.
Intros H'0 H'1; Split; [Auto with sets | Idtac].
Intros z H'2 H'3; Try Assumption.
Elim (classic  x == z); Auto with sets.
Intro H'4; Right; Try Assumption.
Elim (classic  z == y); Auto with sets.
Intro H'5; Try Assumption.
Elim H'1.
Exists z; Auto with sets.
Qed.

Theorem Add_covers:
  (A: (Ensemble U)) (a: (Ensemble U)) (Included U a A) ->
   (x: U) (In U A x) -> ~ (In U a x) ->
    (covers (Ensemble U) (Power_set_PO U A) (Add U a x) a).
Proof.
Intros A a H' x H'0 H'1; Try Assumption.
Apply setcover_intro; Auto with sets.
Red.
Split; [Idtac | Red; Intro H'2; Try Exact H'2]; Auto with sets.
Apply H'1.
Rewrite H'2; Auto with sets.
Red; Intro H'2; Elim H'2; Clear H'2.
Intros z H'2; Elim H'2; Intros H'3 H'4; Try Exact H'3; Clear H'2.
LApply (Strict_Included_inv U a z); Auto with sets; Clear H'3.
Intro H'2; Elim H'2; Intros H'3 H'5; Elim H'5; Clear H'2 H'5.
Intros x0 H'2; Elim H'2.
Intros H'5 H'6; Try Assumption.
Generalize H'4; Intro K.
Red in H'4.
Elim H'4; Intros H'8 H'9; Red in H'8; Clear H'4.
LApply (H'8 x0); Auto with sets.
Intro H'7; Try Assumption.
Elim (Add_inv U a x x0); Auto with sets.
Intro H'15.
Cut (Included U (Add U a x) z).
Intro H'10; Try Assumption.
Red in K.
Elim K; Intros H'11 H'12; Apply H'12; Clear K; Auto with sets.
Rewrite H'15.
Red.
Intros x1 H'10; Elim H'10; Auto with sets.
Intros x2 H'11; Elim H'11; Auto with sets.
Qed.

Theorem covers_Add:
  (A: (Ensemble U))
  (a, a': (Ensemble U))
  (Included U a A) ->
  (Included U a' A) -> (covers (Ensemble U) (Power_set_PO U A) a' a) ->
   (EXT x | a' == (Add U a x) /\ ((In U A x) /\ ~ (In U a x))).
Proof.
Intros A a a' H' H'0 H'1; Try Assumption.
Elim (setcover_inv A a a'); Auto with sets.
Intros H'6 H'7.
Clear H'1.
Elim (Strict_Included_inv U a a'); Auto with sets.
Intros H'5 H'8; Elim H'8.
Intros x H'1; Elim H'1.
Intros H'2 H'3; Try Assumption.
Exists x.
Split; [Try Assumption | Idtac].
Clear H'8 H'1.
Elim (H'7 (Add U a x)); Auto with sets.
Intro H'1.
Absurd a ==(Add U a x); Auto with sets.
Red; Intro H'8; Try Exact H'8.
Apply H'3.
Rewrite H'8; Auto with sets.
Auto with sets.
Red.
Intros x0 H'1; Elim H'1; Auto with sets.
Intros x1 H'8; Elim H'8; Auto with sets.
Split; [Idtac | Try Assumption].
Red in H'0; Auto with sets.
Qed.

Theorem covers_is_Add:
  (A: (Ensemble U))
  (a, a': (Ensemble U)) (Included U a A) -> (Included U a' A) ->
   (iff
      (covers (Ensemble U) (Power_set_PO U A) a' a)
      (EXT x | a' == (Add U a x) /\ ((In U A x) /\ ~ (In U a x)))).
Proof.
Intros A a a' H' H'0; Split; Intro K.
Apply covers_Add with A := A; Auto with sets.
Elim K.
Intros x H'1; Elim H'1; Intros H'2 H'3; Rewrite H'2; Clear H'1.
Apply Add_covers; Intuition.
Qed.

Theorem Singleton_atomic:
  (x:U) (A:(Ensemble U)) (In U A x) ->
  (covers (Ensemble U) (Power_set_PO U A) (Singleton U x) (Empty_set U)).
Intros x A H'.
Rewrite <- (Empty_set_zero' U x).
Apply Add_covers; Auto with sets.
Qed.

Lemma less_than_singleton:
  (X:(Ensemble U)) (x:U) (Strict_Included U X (Singleton U x)) ->
  X ==(Empty_set U).
Intros X x H'; Try Assumption.
Red in H'.
LApply (Singleton_atomic x (Full_set U));
 [Intro H'2; Try Exact H'2 | Apply Full_intro].
Elim H'; Intros H'0 H'1; Try Exact H'1; Clear H'.
Elim (setcover_inv (Full_set U) (Empty_set U) (Singleton U x));
 [Intros H'6 H'7; Try Exact H'7 | Idtac]; Auto with sets.
Elim (H'7 X); [Intro H'5; Try Exact H'5 | Intro H'5 | Idtac | Idtac]; Auto with sets.
Elim H'1; Auto with sets.
Qed.

End Sets_as_an_algebra.

Hints Resolve incl_soustr_in : sets v62.
Hints Resolve incl_soustr : sets v62.
Hints Resolve incl_soustr_add_l : sets v62.
Hints Resolve incl_soustr_add_r : sets v62.
Hints Resolve add_soustr_1 add_soustr_2 : sets v62.
Hints Resolve add_soustr_xy : sets v62.
