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

Section Partial_orders.
Variable U: Type.

Definition Carrier :=  (Ensemble U).

Definition Rel :=  (Relation U).

Record PO : Type := Definition_of_PO {
   Carrier_of: (Ensemble U);
   Rel_of: (Relation U);
   PO_cond1: (Inhabited U Carrier_of);
   PO_cond2: (Order U Rel_of) }.
Variable p: PO.

Definition Strict_Rel_of : Rel :=  [x, y: U] (Rel_of p x y) /\ ~ x == y.

Inductive covers [y, x:U]: Prop :=
      Definition_of_covers:
      (Strict_Rel_of x y) -> 
          ~ (EXT z | (Strict_Rel_of x z) /\ (Strict_Rel_of z y)) -> 
          (covers y x).

End Partial_orders.

Hints Unfold Carrier_of Rel_of  Strict_Rel_of : sets v62.
Hints Resolve Definition_of_covers : sets v62.


Section Partial_order_facts.
Variable U:Type.
Variable D:(PO U).

Lemma Strict_Rel_Transitive_with_Rel:
  (x:U) (y:U) (z:U) (Strict_Rel_of U D x y) -> (Rel_of U D y z) ->
  (Strict_Rel_of U D x z).
Unfold 1 Strict_Rel_of.
Red.
Elim D; Simpl.
Intros C R H' H'0; Elim H'0.
Intros H'1 H'2 H'3 x y z H'4 H'5; Split.
Apply H'2 with y := y; Tauto.
Red; Intro H'6.
Elim H'4; Intros H'7 H'8; Apply H'8; Clear H'4.
Apply H'3; Auto.
Rewrite H'6; Tauto.
Qed.

Lemma Strict_Rel_Transitive_with_Rel_left:
  (x:U) (y:U) (z:U) (Rel_of U D x y) -> (Strict_Rel_of U D y z) ->
  (Strict_Rel_of U D x z).
Unfold 1 Strict_Rel_of.
Red.
Elim D; Simpl.
Intros C R H' H'0; Elim H'0.
Intros H'1 H'2 H'3 x y z H'4 H'5; Split.
Apply H'2 with y := y; Tauto.
Red; Intro H'6.
Elim H'5; Intros H'7 H'8; Apply H'8; Clear H'5.
Apply H'3; Auto.
Rewrite <- H'6; Auto.
Qed.

Lemma Strict_Rel_Transitive: (Transitive U (Strict_Rel_of U D)).
Red.
Intros x y z H' H'0.
Apply Strict_Rel_Transitive_with_Rel with y := y; 
  [ Intuition | Unfold Strict_Rel_of in H' H'0; Intuition ].
Qed.
End Partial_order_facts.
