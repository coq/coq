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
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.

Section The_power_set_partial_order.
Variable U: Type.

Inductive Power_set [A:(Ensemble U)]: (Ensemble (Ensemble U)) :=
    Definition_of_Power_set:
     (X: (Ensemble U)) (Included U X A) -> (In (Ensemble U) (Power_set A) X).
Hints Resolve Definition_of_Power_set.

Theorem Empty_set_minimal: (X: (Ensemble U)) (Included U (Empty_set U) X).
Intro X; Red.
Intros x H'; Elim H'.
Qed.
Hints Resolve Empty_set_minimal.

Theorem Power_set_Inhabited:
  (X: (Ensemble U)) (Inhabited (Ensemble U) (Power_set X)).
Intro X.
Apply Inhabited_intro with (Empty_set U); Auto with sets.
Qed.
Hints Resolve Power_set_Inhabited.

Theorem Inclusion_is_an_order: (Order (Ensemble U) (Included U)).
Auto 6 with sets.
Qed.
Hints Resolve Inclusion_is_an_order.

Theorem Inclusion_is_transitive: (Transitive (Ensemble U) (Included U)).
Elim Inclusion_is_an_order; Auto with sets.
Qed.
Hints Resolve Inclusion_is_transitive.

Definition Power_set_PO: (Ensemble U) -> (PO (Ensemble U)).
Intro A; Try Assumption.
Apply Definition_of_PO with (Power_set A) (Included U); Auto with sets.
Defined.
Hints Unfold  Power_set_PO.

Theorem Strict_Rel_is_Strict_Included:
  (same_relation
     (Ensemble U) (Strict_Included U)
     (Strict_Rel_of (Ensemble U) (Power_set_PO (Full_set U)))).
Auto with sets.
Qed.
Hints Resolve Strict_Rel_Transitive Strict_Rel_is_Strict_Included.

Lemma Strict_inclusion_is_transitive_with_inclusion:
  (x, y, z:(Ensemble U)) (Strict_Included U x y) -> (Included U y z) ->
  (Strict_Included U x z).
Intros x y z H' H'0; Try Assumption.
Elim Strict_Rel_is_Strict_Included.
Unfold contains.
Intros H'1 H'2; Try Assumption.
Apply H'1.
Apply Strict_Rel_Transitive_with_Rel with y := y; Auto with sets.
Qed.

Lemma Strict_inclusion_is_transitive_with_inclusion_left:
  (x, y, z:(Ensemble U)) (Included U x y) -> (Strict_Included U y z) ->
  (Strict_Included U x z).
Intros x y z H' H'0; Try Assumption.
Elim Strict_Rel_is_Strict_Included.
Unfold contains.
Intros H'1 H'2; Try Assumption.
Apply H'1.
Apply Strict_Rel_Transitive_with_Rel_left with y := y; Auto with sets.
Qed.

Lemma Strict_inclusion_is_transitive:
  (Transitive (Ensemble U) (Strict_Included U)).
Apply cong_transitive_same_relation
     with R := (Strict_Rel_of (Ensemble U) (Power_set_PO (Full_set U))); Auto with sets.
Qed.

Theorem Empty_set_is_Bottom:
  (A: (Ensemble U)) (Bottom (Ensemble U) (Power_set_PO A) (Empty_set U)).
Intro A; Apply Bottom_definition; Simpl; Auto with sets.
Qed.
Hints Resolve Empty_set_is_Bottom.

Theorem Union_minimal:
  (a, b, X: (Ensemble U)) (Included U a X) -> (Included U b X) ->
   (Included U (Union U a b) X).
Intros a b X H' H'0; Red.
Intros x H'1; Elim H'1; Auto with sets.
Qed.
Hints Resolve Union_minimal.

Theorem Intersection_maximal:
  (a, b, X: (Ensemble U)) (Included U X a) -> (Included U X b) ->
   (Included U X (Intersection U a b)).
Auto with sets.
Qed.

Theorem Union_increases_l: (a, b: (Ensemble U)) (Included U a (Union U a b)).
Auto with sets.
Qed.

Theorem Union_increases_r: (a, b: (Ensemble U)) (Included U b (Union U a b)).
Auto with sets.
Qed.

Theorem Intersection_decreases_l:
  (a, b: (Ensemble U)) (Included U (Intersection U a b) a).
Intros a b; Red.
Intros x H'; Elim H'; Auto with sets.
Qed.

Theorem Intersection_decreases_r:
  (a, b: (Ensemble U)) (Included U (Intersection U a b) b).
Intros a b; Red.
Intros x H'; Elim H'; Auto with sets.
Qed.
Hints Resolve Union_increases_l Union_increases_r Intersection_decreases_l
     Intersection_decreases_r.

Theorem Union_is_Lub:
  (A: (Ensemble U)) (a, b: (Ensemble U)) (Included U a A) -> (Included U b A) ->
   (Lub (Ensemble U) (Power_set_PO A) (Couple (Ensemble U) a b) (Union U a b)).
Intros A a b H' H'0.
Apply Lub_definition; Simpl.
Apply Upper_Bound_definition; Simpl; Auto with sets.
Intros y H'1; Elim H'1; Auto with sets.
Intros y H'1; Elim H'1; Simpl; Auto with sets.
Qed.

Theorem Intersection_is_Glb:
  (A: (Ensemble U)) (a, b: (Ensemble U)) (Included U a A) -> (Included U b A) ->
   (Glb
      (Ensemble U)
      (Power_set_PO A)
      (Couple (Ensemble U) a b)
      (Intersection U a b)).
Intros A a b H' H'0.
Apply Glb_definition; Simpl.
Apply Lower_Bound_definition; Simpl; Auto with sets.
Apply Definition_of_Power_set.
Generalize Inclusion_is_transitive; Intro IT; Red in IT; Apply IT with a; Auto with sets.
Intros y H'1; Elim H'1; Auto with sets.
Intros y H'1; Elim H'1; Simpl; Auto with sets.
Qed.

End The_power_set_partial_order.

Hints Resolve Empty_set_minimal : sets v62.
Hints Resolve Power_set_Inhabited : sets v62.
Hints Resolve Inclusion_is_an_order : sets v62.
Hints Resolve Inclusion_is_transitive : sets v62.
Hints Resolve Union_minimal : sets v62.
Hints Resolve Union_increases_l : sets v62.
Hints Resolve Union_increases_r : sets v62.
Hints Resolve Intersection_decreases_l : sets v62.
Hints Resolve Intersection_decreases_r : sets v62.
Hints Resolve Empty_set_is_Bottom : sets v62.
Hints Resolve Strict_inclusion_is_transitive : sets v62.
