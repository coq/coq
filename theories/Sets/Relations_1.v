(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
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

Section Relations_1.
   Variable U: Type.
   
   Definition Relation :=  U -> U -> Prop.
   Variable R: Relation.
   
   Definition Reflexive : Prop :=  (x: U) (R x x).
   
   Definition Transitive : Prop :=  (x,y,z: U) (R x y) -> (R y z) -> (R x z).
   
   Definition Symmetric : Prop :=  (x,y: U) (R x y) -> (R y x).
   
   Definition Antisymmetric : Prop :=
      (x: U) (y: U) (R x y) -> (R y x) -> x == y.
   
   Definition contains : Relation -> Relation -> Prop :=
      [R,R': Relation] (x: U) (y: U) (R' x y) -> (R x y).
   
   Definition same_relation : Relation -> Relation -> Prop :=
      [R,R': Relation] (contains R R') /\ (contains R' R).
   
   Inductive Preorder : Prop :=
         Definition_of_preorder: Reflexive -> Transitive -> Preorder.
   
   Inductive Order : Prop :=
         Definition_of_order: Reflexive -> Transitive -> Antisymmetric -> Order.
   
   Inductive Equivalence : Prop :=
         Definition_of_equivalence:
           Reflexive -> Transitive -> Symmetric -> Equivalence.
   
   Inductive PER : Prop :=
         Definition_of_PER: Symmetric -> Transitive -> PER.
   
End Relations_1.
Hints Unfold Reflexive Transitive Antisymmetric Symmetric contains 
	same_relation : sets v62.
Hints Resolve Definition_of_preorder Definition_of_order 
	Definition_of_equivalence Definition_of_PER : sets v62.
