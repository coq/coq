(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Section Relation_Definition.

   Variable A: Set.
   
   Definition relation :=  A -> A -> Prop.

   Variable R: relation.
   

Section General_Properties_of_Relations.

  Definition reflexive : Prop :=  (x: A) (R x x).
  Definition transitive : Prop :=  (x,y,z: A) (R x y) -> (R y z) -> (R x z).
  Definition symmetric : Prop :=  (x,y: A) (R x y) -> (R y x).
  Definition antisymmetric : Prop :=  (x,y: A) (R x y) -> (R y x) -> x=y.

  (* for compatibility with Equivalence in  ../PROGRAMS/ALG/  *)
  Definition equiv := reflexive /\ transitive /\ symmetric.

End General_Properties_of_Relations.



Section Sets_of_Relations.

   Record preorder : Prop := {
       preord_refl  : reflexive;
       preord_trans : transitive }.

   Record order : Prop := {
       ord_refl    : reflexive;
       ord_trans   : transitive;
       ord_antisym : antisymmetric }.

   Record equivalence : Prop := {
       equiv_refl  : reflexive;
       equiv_trans : transitive;
       equiv_sym   : symmetric }.
   
   Record PER : Prop := {
       per_sym   : symmetric;
       per_trans : transitive }.

End Sets_of_Relations.



Section Relations_of_Relations.

  Definition inclusion : relation -> relation -> Prop :=
      [R1,R2: relation] (x,y:A) (R1 x y) -> (R2 x y).

  Definition same_relation : relation -> relation -> Prop :=
      [R1,R2: relation] (inclusion R1 R2) /\ (inclusion R2 R1).
   
  Definition commut : relation -> relation -> Prop :=
      [R1,R2:relation] (x,y:A) (R1 y x) -> (z:A) (R2 z y)
                          -> (EX y':A |(R2 y' x) & (R1 z y')).

End Relations_of_Relations.

   
End Relation_Definition.

Hints Unfold reflexive transitive antisymmetric symmetric : sets v62.

Hints Resolve Build_preorder Build_order Build_equivalence 
	Build_PER preord_refl preord_trans 
	ord_refl ord_trans ord_antisym
	equiv_refl equiv_trans equiv_sym
	per_sym per_trans : sets v62.

Hints Unfold inclusion same_relation commut : sets v62.
