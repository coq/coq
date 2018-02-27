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
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.

Section The_power_set_partial_order.
Variable U : Type.

Inductive Power_set (A:Ensemble U) : Ensemble (Ensemble U) :=
    Definition_of_Power_set :
      forall X:Ensemble U, Included U X A -> In (Ensemble U) (Power_set A) X.
Hint Resolve Definition_of_Power_set.

Theorem Empty_set_minimal : forall X:Ensemble U, Included U (Empty_set U) X.
intro X; red.
intros x H'; elim H'.
Qed.
Hint Resolve Empty_set_minimal.

Theorem Power_set_Inhabited :
 forall X:Ensemble U, Inhabited (Ensemble U) (Power_set X).
intro X.
apply Inhabited_intro with (Empty_set U); auto with sets.
Qed.
Hint Resolve Power_set_Inhabited.

Theorem Inclusion_is_an_order : Order (Ensemble U) (Included U).
auto 6 with sets.
Qed.
Hint Resolve Inclusion_is_an_order.

Theorem Inclusion_is_transitive : Transitive (Ensemble U) (Included U).
elim Inclusion_is_an_order; auto with sets.
Qed.
Hint Resolve Inclusion_is_transitive.

Definition Power_set_PO : Ensemble U -> PO (Ensemble U).
intro A; try assumption.
apply Definition_of_PO with (Power_set A) (Included U); auto with sets.
Defined.
Hint Unfold Power_set_PO.

Theorem Strict_Rel_is_Strict_Included :
 same_relation (Ensemble U) (Strict_Included U)
   (Strict_Rel_of (Ensemble U) (Power_set_PO (Full_set U))).
auto with sets.
Qed.
Hint Resolve Strict_Rel_Transitive Strict_Rel_is_Strict_Included.

Lemma Strict_inclusion_is_transitive_with_inclusion :
 forall x y z:Ensemble U,
   Strict_Included U x y -> Included U y z -> Strict_Included U x z.
intros x y z H' H'0; try assumption.
elim Strict_Rel_is_Strict_Included.
unfold contains.
intros H'1 H'2; try assumption.
apply H'1.
apply Strict_Rel_Transitive_with_Rel with (y := y); auto with sets.
Qed.

Lemma Strict_inclusion_is_transitive_with_inclusion_left :
 forall x y z:Ensemble U,
   Included U x y -> Strict_Included U y z -> Strict_Included U x z.
intros x y z H' H'0; try assumption.
elim Strict_Rel_is_Strict_Included.
unfold contains.
intros H'1 H'2; try assumption.
apply H'1.
apply Strict_Rel_Transitive_with_Rel_left with (y := y); auto with sets.
Qed.

Lemma Strict_inclusion_is_transitive :
 Transitive (Ensemble U) (Strict_Included U).
apply cong_transitive_same_relation with
 (R := Strict_Rel_of (Ensemble U) (Power_set_PO (Full_set U)));
 auto with sets.
Qed.

Theorem Empty_set_is_Bottom :
 forall A:Ensemble U, Bottom (Ensemble U) (Power_set_PO A) (Empty_set U).
intro A; apply Bottom_definition; simpl; auto with sets.
Qed.
Hint Resolve Empty_set_is_Bottom.

Theorem Union_minimal :
 forall a b X:Ensemble U,
   Included U a X -> Included U b X -> Included U (Union U a b) X.
intros a b X H' H'0; red.
intros x H'1; elim H'1; auto with sets.
Qed.
Hint Resolve Union_minimal.

Theorem Intersection_maximal :
 forall a b X:Ensemble U,
   Included U X a -> Included U X b -> Included U X (Intersection U a b).
auto with sets.
Qed.

Theorem Union_increases_l : forall a b:Ensemble U, Included U a (Union U a b).
auto with sets.
Qed.

Theorem Union_increases_r : forall a b:Ensemble U, Included U b (Union U a b).
auto with sets.
Qed.

Theorem Intersection_decreases_l :
 forall a b:Ensemble U, Included U (Intersection U a b) a.
intros a b; red.
intros x H'; elim H'; auto with sets.
Qed.

Theorem Intersection_decreases_r :
 forall a b:Ensemble U, Included U (Intersection U a b) b.
intros a b; red.
intros x H'; elim H'; auto with sets.
Qed.
Hint Resolve Union_increases_l Union_increases_r Intersection_decreases_l
  Intersection_decreases_r.

Theorem Union_is_Lub :
 forall A a b:Ensemble U,
   Included U a A ->
   Included U b A ->
   Lub (Ensemble U) (Power_set_PO A) (Couple (Ensemble U) a b) (Union U a b).
intros A a b H' H'0.
apply Lub_definition; simpl.
apply Upper_Bound_definition; simpl; auto with sets.
intros y H'1; elim H'1; auto with sets.
intros y H'1; elim H'1; simpl; auto with sets.
Qed.

Theorem Intersection_is_Glb :
 forall A a b:Ensemble U,
   Included U a A ->
   Included U b A ->
   Glb (Ensemble U) (Power_set_PO A) (Couple (Ensemble U) a b)
     (Intersection U a b).
intros A a b H' H'0.
apply Glb_definition; simpl.
apply Lower_Bound_definition; simpl; auto with sets.
apply Definition_of_Power_set.
generalize Inclusion_is_transitive; intro IT; red in IT; apply IT with a;
 auto with sets.
intros y H'1; elim H'1; auto with sets.
intros y H'1; elim H'1; simpl; auto with sets.
Qed.

End The_power_set_partial_order.

Hint Resolve Empty_set_minimal: sets.
Hint Resolve Power_set_Inhabited: sets.
Hint Resolve Inclusion_is_an_order: sets.
Hint Resolve Inclusion_is_transitive: sets.
Hint Resolve Union_minimal: sets.
Hint Resolve Union_increases_l: sets.
Hint Resolve Union_increases_r: sets.
Hint Resolve Intersection_decreases_l: sets.
Hint Resolve Intersection_decreases_r: sets.
Hint Resolve Empty_set_is_Bottom: sets.
Hint Resolve Strict_inclusion_is_transitive: sets.
