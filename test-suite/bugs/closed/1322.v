Require Import Setoid.

Section transition_gen.

Variable I : Type.
Variable I_eq :I -> I -> Prop.
Variable I_eq_equiv : Setoid_Theory I I_eq.

(* Add Relation I I_eq
  reflexivity proved by I_eq_equiv.(Seq_refl I I_eq)
  symmetry proved by I_eq_equiv.(Seq_sym I I_eq)
  transitivity proved by I_eq_equiv.(Seq_trans I I_eq)
as I_eq_relation. *)

Add Parametric Relation : I I_eq
  reflexivity  proved by I_eq_equiv.(@Equivalence_Reflexive _ _)
  symmetry     proved by I_eq_equiv.(@Equivalence_Symmetric _ _)
  transitivity proved by I_eq_equiv.(@Equivalence_Transitive _ _)
  as I_with_eq.

Variable F : I -> Type.
Variable F_morphism : forall i j, I_eq i j -> F i = F j.


Add Morphism F with signature I_eq ==> (@eq _) as F_morphism2.
Admitted.

End transition_gen.
