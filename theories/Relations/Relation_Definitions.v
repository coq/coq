(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** *** Properties of relations over a domain (endorelations) *)

Set Implicit Arguments.
Set Strict Implicit.

Section Endorelation_Definition.

  Variable A : Type.

  Definition relation := A -> A -> Prop.

(** General properties of relations *)

Section General_Properties_of_Endorelations.

  Variable R : relation.
   
  Definition reflexive : Prop := forall x:A, R x x.
  Definition transitive : Prop := forall x y z:A, R x y -> R y z -> R x z.
  Definition symmetric : Prop := forall x y:A, R x y -> R y x.
  Definition antisymmetric : Prop := forall x y:A, R x y -> R y x -> x = y.
  Definition asymmetric : Prop := forall x y:A, R x y -> ~ R y x.
  Definition irreflexive : Prop := forall x y:A, ~ R x x.

  Record preorder : Prop := 
    {preord_refl : reflexive; 
     preord_trans : transitive}.

  Record order : Prop := 
    {ord_refl : reflexive;
     ord_trans : transitive;
     ord_antisym : antisymmetric}.

  Record strict_order : Prop := 
    {stord_irrefl : irreflexive;
     stord_trans : transitive;
     stord_sym : asymmetric}.

  Record equivalence : Prop := 
    {equiv_refl : reflexive;
     equiv_trans : transitive;
     equiv_sym : symmetric}.
   
  Record PER : Prop :=
    {per_sym : symmetric; 
     per_trans : transitive}.

End General_Properties_of_Endorelations.

End Endorelation_Definition.

Hint Unfold reflexive transitive antisymmetric symmetric: sets v62.

Hint Resolve Build_preorder Build_order Build_equivalence Build_PER
  preord_refl preord_trans ord_refl ord_trans ord_antisym equiv_refl
  equiv_trans equiv_sym per_sym per_trans: sets v62.

(** *** Properties of arbitrary relations *)

Section Relation_Definition.

  Variables A B : Type.

  Variable R : A -> B -> Prop.

  Definition univalent : Prop := 
    forall x:A, forall y z:B, R x y -> R x z -> y=z.

  (** Relations between relations *)

  Section Relations_of_Relations.

    Definition inclusion (R1 R2 : A->B->Prop) :=
      forall x y, R1 x y -> R2 x y.

    Definition same_relation (R1 R2 : A->B->Prop) :=
      inclusion R1 R2 /\ inclusion R2 R1.

    Definition commut (R1 : A->A->Prop) (R2 : A->A->Prop) :=
      forall x y,
        R1 x y -> forall z, R2 y z -> exists2 y' : A, R2 x y' & R1 y' z.

  End Relations_of_Relations.
   
End Relation_Definition.

Hint Unfold inclusion same_relation commut: sets v62.

(* Compatibility notes

  [commut] was written with x and z, and R2 and R1 swapped.

*)
