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
Require Export Image.

Section Approx.
Variable U: Type.

Inductive Approximant [A, X:(Ensemble U)] : Prop :=
  Defn_of_Approximant: (Finite U X) -> (Included U X A) -> (Approximant A X).
End Approx.

Hints Resolve Defn_of_Approximant.

Section Infinite_sets.
Variable U: Type.

Lemma make_new_approximant:
  (A: (Ensemble U)) (X: (Ensemble U)) ~ (Finite U A) -> (Approximant U A X) ->
   (Inhabited U (Setminus U A X)).
Proof.
Intros A X H' H'0.
Elim H'0; Intros H'1 H'2.
Apply Strict_super_set_contains_new_element; Auto with sets.
Red; Intro H'3; Apply H'.
Rewrite <- H'3; Auto with sets.
Qed.

Lemma approximants_grow:
  (A: (Ensemble U)) (X: (Ensemble U)) ~ (Finite U A) ->
   (n: nat) (cardinal U X n) -> (Included U X A) ->
    (EXT Y | (cardinal U Y (S n)) /\ (Included U Y A)).
Proof.
Intros A X H' n H'0; Elim H'0; Auto with sets.
Intro H'1.
Cut (Inhabited U (Setminus U A (Empty_set U))).
Intro H'2; Elim H'2.
Intros x H'3.
Exists (Add U (Empty_set U) x); Auto with sets.
Split.
Apply card_add; Auto with sets.
Cut (In U A x).
Intro H'4; Red; Auto with sets.
Intros x0 H'5; Elim H'5; Auto with sets.
Intros x1 H'6; Elim H'6; Auto with sets.
Elim H'3; Auto with sets.
Apply make_new_approximant; Auto with sets.
Intros A0 n0 H'1 H'2 x H'3 H'5.
LApply H'2; [Intro H'6; Elim H'6; Clear H'2 | Clear H'2]; Auto with sets.
Intros x0 H'2; Try Assumption.
Elim H'2; Intros H'7 H'8; Try Exact H'8; Clear H'2.
Elim (make_new_approximant A x0); Auto with sets.
Intros x1 H'2; Try Assumption.
Exists (Add U x0 x1); Auto with sets.
Split.
Apply card_add; Auto with sets.
Elim H'2; Auto with sets.
Red.
Intros x2 H'9; Elim H'9; Auto with sets.
Intros x3 H'10; Elim H'10; Auto with sets.
Elim H'2; Auto with sets.
Auto with sets.
Apply Defn_of_Approximant; Auto with sets.
Apply cardinal_finite with n := (S n0); Auto with sets.
Qed.

Lemma approximants_grow':
  (A: (Ensemble U)) (X: (Ensemble U)) ~ (Finite U A) ->
   (n: nat) (cardinal U X n) -> (Approximant U A X) ->
    (EXT Y | (cardinal U Y (S n)) /\ (Approximant U A Y)).
Proof.
Intros A X H' n H'0 H'1; Try Assumption.
Elim H'1.
Intros H'2 H'3.
ElimType (EXT Y | (cardinal U Y (S n)) /\ (Included U Y A)).
Intros x H'4; Elim H'4; Intros H'5 H'6; Try Exact H'5; Clear H'4.
Exists x; Auto with sets.
Split; [Auto with sets | Idtac].
Apply Defn_of_Approximant; Auto with sets.
Apply cardinal_finite with n := (S n); Auto with sets.
Apply approximants_grow with X := X; Auto with sets.
Qed.

Lemma approximant_can_be_any_size:
  (A: (Ensemble U)) (X: (Ensemble U)) ~ (Finite U A) ->
   (n: nat) (EXT Y | (cardinal U Y n) /\ (Approximant U A Y)).
Proof.
Intros A H' H'0 n; Elim n.
Exists (Empty_set U); Auto with sets.
Intros n0 H'1; Elim H'1.
Intros x H'2.
Apply approximants_grow' with X := x; Tauto.
Qed.

Variable V: Type.

Theorem Image_set_continuous:
  (A: (Ensemble U))
  (f: U -> V) (X: (Ensemble V)) (Finite V X) -> (Included V X (Im U V A f)) ->
   (EX n |
   (EXT Y | ((cardinal U Y n) /\ (Included U Y A)) /\ (Im U V Y f) == X)).
Proof.
Intros A f X H'; Elim H'.
Intro H'0; Exists O.
Exists (Empty_set U); Auto with sets.
Intros A0 H'0 H'1 x H'2 H'3; Try Assumption.
LApply H'1;
 [Intro H'4; Elim H'4; Intros n E; Elim E; Clear H'4 H'1 | Clear H'1]; Auto with sets.
Intros x0 H'1; Try Assumption.
Exists (S n); Try Assumption.
Elim H'1; Intros H'4 H'5; Elim H'4; Intros H'6 H'7; Try Exact H'6; Clear H'4 H'1.
Clear E.
Generalize H'2.
Rewrite <- H'5.
Intro H'1; Try Assumption.
Red in H'3.
Generalize (H'3 x).
Intro H'4; LApply H'4; [Intro H'8; Try Exact H'8; Clear H'4 | Clear H'4]; Auto with sets.
Specialize 5 Im_inv with U := U V:=V X := A f := f y := x; Intro H'11; 
 LApply H'11; [Intro H'13; Elim H'11; Clear H'11 | Clear H'11]; Auto with sets.
Intros x1 H'4; Try Assumption.
Apply exT_intro with x := (Add U x0 x1).
Split; [Split; [Try Assumption | Idtac] | Idtac].
Apply card_add; Auto with sets.
Red; Intro H'9; Try Exact H'9.
Apply H'1.
Elim H'4; Intros H'10 H'11; Rewrite <- H'11; Clear H'4; Auto with sets.
Elim H'4; Intros H'9 H'10; Try Exact H'9; Clear H'4; Auto with sets.
Red; Auto with sets.
Intros x2 H'4; Elim H'4; Auto with sets.
Intros x3 H'11; Elim H'11; Auto with sets.
Elim H'4; Intros H'9 H'10; Rewrite <- H'10; Clear H'4; Auto with sets.
Apply Im_add; Auto with sets.
Qed.

Theorem Image_set_continuous':
  (A: (Ensemble U))
  (f: U -> V) (X: (Ensemble V)) (Approximant V (Im U V A f) X) ->
   (EXT Y | (Approximant U A Y) /\ (Im U V Y f) == X).
Proof.
Intros A f X H'; Try Assumption.
Cut (EX n | (EXT Y |
    ((cardinal U Y n) /\ (Included U Y A)) /\ (Im U V Y f) == X)).
Intro H'0; Elim H'0; Intros n E; Elim E; Clear H'0.
Intros x H'0; Try Assumption.
Elim H'0; Intros H'1 H'2; Elim H'1; Intros H'3 H'4; Try Exact H'3;
 Clear H'1 H'0; Auto with sets.
Exists x.
Split; [Idtac | Try Assumption].
Apply Defn_of_Approximant; Auto with sets.
Apply cardinal_finite with n := n; Auto with sets.
Apply Image_set_continuous; Auto with sets.
Elim H'; Auto with sets.
Elim H'; Auto with sets.
Qed.

Theorem Pigeonhole_bis:
  (A: (Ensemble U)) (f: U -> V) ~ (Finite U A) -> (Finite V (Im U V A f)) ->
   ~ (injective U V f).
Proof.
Intros A f H'0 H'1; Try Assumption.
Elim (Image_set_continuous' A f (Im U V A f)); Auto with sets.
Intros x H'2; Elim H'2; Intros H'3 H'4; Try Exact H'3; Clear H'2.
Elim (make_new_approximant A x); Auto with sets.
Intros x0 H'2; Elim H'2.
Intros H'5 H'6.
Elim (finite_cardinal V (Im U V A f)); Auto with sets.
Intros n E.
Elim (finite_cardinal U x); Auto with sets.
Intros n0 E0.
Apply Pigeonhole with A := (Add U x x0) n := (S n0) n' := n.
Apply card_add; Auto with sets.
Rewrite (Im_add U V x x0 f); Auto with sets.
Cut (In V (Im U V x f) (f x0)).
Intro H'8.
Rewrite (Non_disjoint_union V (Im U V x f) (f x0)); Auto with sets.
Rewrite H'4; Auto with sets.
Elim (Extension V (Im U V x f) (Im U V A f)); Auto with sets.
Apply le_lt_n_Sm.
Apply cardinal_decreases with U := U V := V A := x f := f; Auto with sets.
Rewrite H'4; Auto with sets.
Elim H'3; Auto with sets.
Qed.

Theorem Pigeonhole_ter:
  (A: (Ensemble U))
  (f: U -> V) (n: nat) (injective U V f) -> (Finite V (Im U V A f)) ->
   (Finite U A).
Proof.
Intros A f H' H'0 H'1.
Apply NNPP.
Red; Intro H'2.
Elim (Pigeonhole_bis A f); Auto with sets.
Qed.

End Infinite_sets.
