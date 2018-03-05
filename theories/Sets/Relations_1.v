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

Section Relations_1.
   Variable U : Type.

   Definition Relation := U -> U -> Prop.
   Variable R : Relation.

   Definition Reflexive : Prop := forall x:U, R x x.

   Definition Transitive : Prop := forall x y z:U, R x y -> R y z -> R x z.

   Definition Symmetric : Prop := forall x y:U, R x y -> R y x.

   Definition Antisymmetric : Prop := forall x y:U, R x y -> R y x -> x = y.

   Definition contains (R R':Relation) : Prop :=
     forall x y:U, R' x y -> R x y.

   Definition same_relation (R R':Relation) : Prop :=
     contains R R' /\ contains R' R.

   Inductive Preorder : Prop :=
       Definition_of_preorder : Reflexive -> Transitive -> Preorder.

   Inductive Order : Prop :=
       Definition_of_order :
         Reflexive -> Transitive -> Antisymmetric -> Order.

   Inductive Equivalence : Prop :=
       Definition_of_equivalence :
         Reflexive -> Transitive -> Symmetric -> Equivalence.

   Inductive PER : Prop :=
       Definition_of_PER : Symmetric -> Transitive -> PER.

End Relations_1.
Hint Unfold Reflexive Transitive Antisymmetric Symmetric contains
  same_relation: sets.
Hint Resolve Definition_of_preorder Definition_of_order
  Definition_of_equivalence Definition_of_PER: sets.
