Require Import Setoid.

Parameter value' : Type.
Parameter equiv' : value' -> value' -> Prop.
Axiom cheat : forall {A}, A.
Add Parametric Relation : _ equiv'
  reflexivity proved by (Equivalence.equiv_reflexive cheat)
  transitivity proved by (Equivalence.equiv_transitive cheat)
    as apply_equiv'_rel.
Check apply_equiv'_rel : PreOrder equiv'.
