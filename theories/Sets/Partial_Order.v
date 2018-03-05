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

Section Partial_orders.
  Variable U : Type.

  Definition Carrier := Ensemble U.

  Definition Rel := Relation U.

  Record PO : Type := Definition_of_PO
    { Carrier_of : Ensemble U;
      Rel_of : Relation U;
      PO_cond1 : Inhabited U Carrier_of;
      PO_cond2 : Order U Rel_of }.
  Variable p : PO.

  Definition Strict_Rel_of : Rel := fun x y:U => Rel_of p x y /\ x <> y.

  Inductive covers (y x:U) : Prop :=
    Definition_of_covers :
    Strict_Rel_of x y ->
    ~ (exists z : _, Strict_Rel_of x z /\ Strict_Rel_of z y) ->
    covers y x.

End Partial_orders.

Hint Unfold Carrier_of Rel_of Strict_Rel_of: sets.
Hint Resolve Definition_of_covers: sets.


Section Partial_order_facts.
  Variable U : Type.
  Variable D : PO U.

  Lemma Strict_Rel_Transitive_with_Rel :
    forall x y z:U,
      Strict_Rel_of U D x y -> @Rel_of U D y z -> Strict_Rel_of U D x z.
  Proof.
    unfold Strict_Rel_of at 1.
    red.
    elim D; simpl.
    intros C R H' H'0; elim H'0.
    intros H'1 H'2 H'3 x y z H'4 H'5; split.
    apply H'2 with (y := y); tauto.
    red; intro H'6.
    elim H'4; intros H'7 H'8; apply H'8; clear H'4.
    apply H'3; auto.
    rewrite H'6; tauto.
  Qed.

  Lemma Strict_Rel_Transitive_with_Rel_left :
    forall x y z:U,
      @Rel_of U D x y -> Strict_Rel_of U D y z -> Strict_Rel_of U D x z.
  Proof.
    unfold Strict_Rel_of at 1.
    red.
    elim D; simpl.
    intros C R H' H'0; elim H'0.
    intros H'1 H'2 H'3 x y z H'4 H'5; split.
    apply H'2 with (y := y); tauto.
    red; intro H'6.
    elim H'5; intros H'7 H'8; apply H'8; clear H'5.
    apply H'3; auto.
    rewrite <- H'6; auto.
  Qed.

  Lemma Strict_Rel_Transitive : Transitive U (Strict_Rel_of U D).
    red.
    intros x y z H' H'0.
    apply Strict_Rel_Transitive_with_Rel with (y := y);
      [ intuition | unfold Strict_Rel_of in H', H'0; intuition ].
  Qed.
End Partial_order_facts.
