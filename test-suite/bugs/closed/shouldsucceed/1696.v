Require Import Setoid.

Inductive mynat := z : mynat | s : mynat -> mynat.

Parameter E : mynat -> mynat -> Prop.
Axiom E_equiv : equiv mynat E.

Add Relation mynat E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Notation "x == y" := (E x y) (at level 70).

Goal z == s z -> s z == z. intros H. setoid_rewrite H at 2. reflexivity. Qed.
