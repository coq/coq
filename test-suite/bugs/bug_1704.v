Require Import TestSuite.admit.

Require Import Setoid.
Parameter E : nat -> nat -> Prop.
Axiom E_equiv : equiv nat E.
Add Relation nat E
reflexivity proved by (proj1 E_equiv)
symmetry proved by (proj2 (proj2 E_equiv))
transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.
Notation "x == y" := (E x y) (at level 70, no associativity).
Axiom r : False -> 0 == 1.
Goal 0 == 0.
Proof.
rewrite r.
reflexivity.
admit.
Qed.
