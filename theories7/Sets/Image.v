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

Require Export Finite_sets.
Require Export Constructive_sets.
Require Export Classical_Type.
Require Export Classical_sets.
Require Export Powerset.
Require Export Powerset_facts.
Require Export Powerset_Classical_facts.
Require Export Gt.
Require Export Lt.
Require Export Le.
Require Export Finite_sets_facts.

Section Image.
Variables U, V: Type.

Inductive Im [X:(Ensemble U); f:U -> V]: (Ensemble V) :=
      Im_intro: (x: U) (In ? X x) -> (y: V) y == (f x) -> (In ? (Im X f) y).

Lemma Im_def:
  (X: (Ensemble U)) (f: U -> V) (x: U) (In ? X x) -> (In ? (Im X f) (f x)).
Proof.
Intros X f x H'; Try Assumption.
Apply Im_intro with x := x; Auto with sets.
Qed.
Hints Resolve Im_def.

Lemma Im_add:
  (X: (Ensemble U)) (x: U) (f: U -> V)
      (Im (Add ? X x) f) == (Add ? (Im X f) (f x)).
Proof.
Intros X x f.
Apply Extensionality_Ensembles.
Split; Red; Intros x0 H'.
Elim H'; Intros.
Rewrite H0.
Elim Add_inv with U X x x1; Auto with sets.
NewDestruct 1; Auto with sets.
Elim Add_inv with V (Im X f) (f x) x0; Auto with sets.
NewDestruct 1 as [x0 H y H0].
Rewrite H0; Auto with sets.
NewDestruct 1; Auto with sets.
Qed.

Lemma image_empty: (f: U -> V) (Im (Empty_set U) f) == (Empty_set V).
Proof.
Intro f; Try Assumption.
Apply Extensionality_Ensembles.
Split; Auto with sets.
Red.
Intros x H'; Elim H'.
Intros x0 H'0; Elim H'0; Auto with sets.
Qed.
Hints Resolve image_empty.

Lemma finite_image:
  (X: (Ensemble U)) (f: U -> V) (Finite ? X) -> (Finite ? (Im X f)).
Proof.
Intros X f H'; Elim H'.
Rewrite (image_empty f); Auto with sets.
Intros A H'0 H'1 x H'2; Clear H' X.
Rewrite (Im_add A x f); Auto with sets.
Apply Add_preserves_Finite; Auto with sets.
Qed.
Hints Resolve finite_image.

Lemma Im_inv:
  (X: (Ensemble U)) (f: U -> V) (y: V) (In ? (Im X f) y) ->
   (exT ? [x: U] (In ? X x) /\ (f x) == y).
Proof.
Intros X f y H'; Elim H'.
Intros x H'0 y0 H'1; Rewrite H'1.
Exists x; Auto with sets.
Qed.

Definition injective :=  [f: U -> V] (x, y: U) (f x) == (f y) -> x == y.

Lemma not_injective_elim:
  (f: U -> V) ~ (injective f) ->
   (EXT x | (EXT y | (f x) == (f y) /\ ~ x == y)).
Proof.
Unfold injective; Intros f H.
Cut (EXT x | ~ ((y: U) (f x) == (f y) -> x == y)).
2: Apply not_all_ex_not with P:=[x:U](y: U) (f x) == (f y) -> x == y; 
   Trivial with sets.
NewDestruct 1 as [x C]; Exists x.
Cut (EXT y | ~((f x)==(f y)->x==y)).
2: Apply not_all_ex_not with P:=[y:U](f x)==(f y)->x==y; Trivial with sets.
NewDestruct 1 as [y D]; Exists y.
Apply imply_to_and; Trivial with sets.
Qed.

Lemma cardinal_Im_intro:
  (A: (Ensemble U)) (f: U -> V) (n: nat) (cardinal ? A n) ->
   (EX p: nat | (cardinal ? (Im A f) p)).
Proof.
Intros.
Apply finite_cardinal; Apply finite_image.
Apply cardinal_finite with n; Trivial with sets.
Qed.

Lemma In_Image_elim:
  (A: (Ensemble U)) (f: U -> V) (injective f) ->
   (x: U) (In ? (Im A f) (f x)) -> (In ? A x).
Proof.
Intros.
Elim Im_inv with A f (f x); Trivial with sets.
Intros z C; Elim C; Intros InAz E.
Elim (H z x E); Trivial with sets.
Qed.

Lemma injective_preserves_cardinal:
  (A: (Ensemble U)) (f: U -> V) (n: nat) (injective f) -> (cardinal ? A n) ->
   (n': nat) (cardinal ? (Im A f) n') -> n' = n.
Proof.
NewInduction 2 as [|A n H'0 H'1 x H'2]; Auto with sets.
Rewrite (image_empty f).
Intros n' CE.
Apply cardinal_unicity with V (Empty_set V); Auto with sets.
Intro n'.
Rewrite (Im_add A x f).
Intro H'3.
Elim cardinal_Im_intro with A f n; Trivial with sets.
Intros i CI.
LApply (H'1 i); Trivial with sets.
Cut ~ (In ? (Im A f) (f x)).
Intros H0 H1.
Apply cardinal_unicity with V (Add ? (Im A f) (f x)); Trivial with sets.
Apply card_add; Auto with sets.
Rewrite <- H1; Trivial with sets.
Red; Intro; Apply H'2.
Apply In_Image_elim with f; Trivial with sets.
Qed.

Lemma cardinal_decreases:
  (A: (Ensemble U)) (f: U -> V) (n: nat) (cardinal U A n) ->
   (n': nat) (cardinal V (Im A f) n') -> (le n' n).
Proof.
NewInduction 1 as [|A n H'0 H'1 x H'2]; Auto with sets.
Rewrite (image_empty f); Intros.
Cut n' = O.
Intro E; Rewrite E; Trivial with sets.
Apply cardinal_unicity with V (Empty_set V); Auto with sets.
Intro n'.
Rewrite (Im_add A x f).
Elim cardinal_Im_intro with A f n; Trivial with sets.
Intros p C H'3.
Apply le_trans with (S p).
Apply card_Add_gen with V (Im A f) (f x); Trivial with sets.
Apply le_n_S; Auto with sets.
Qed.

Theorem Pigeonhole:
  (A: (Ensemble U)) (f: U -> V) (n: nat) (cardinal U A n) ->
   (n': nat) (cardinal V (Im A f) n') -> (lt n' n) -> ~ (injective f).
Proof.
Unfold not; Intros A f n CAn n' CIfn' ltn'n I.
Cut n' = n.
Intro E; Generalize ltn'n; Rewrite E; Exact (lt_n_n n).
Apply injective_preserves_cardinal with A := A f := f n := n; Trivial with sets.
Qed.

Lemma Pigeonhole_principle:
  (A: (Ensemble U)) (f: U -> V) (n: nat) (cardinal ? A n) ->
   (n': nat) (cardinal ? (Im A f) n') -> (lt n' n) ->
    (EXT x | (EXT y | (f x) == (f y) /\ ~ x == y)).
Proof.
Intros; Apply not_injective_elim.
Apply Pigeonhole with A n n'; Trivial with sets.
Qed.
End Image.
Hints Resolve Im_def image_empty finite_image : sets v62.
