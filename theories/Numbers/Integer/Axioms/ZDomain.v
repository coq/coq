Require Import NumPrelude.

Module Type DomainSignature.

Parameter Z : Set.
Parameter E : relation Z.
Parameter e : Z -> Z -> bool.

Axiom E_equiv_e : forall x y : Z, E x y <-> e x y.
Axiom E_equiv : equiv Z E.

Add Relation Z E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

Notation "x == y" := (E x y) (at level 70).
Notation "x # y" := (~ E x y) (at level 70).

End DomainSignature.

Module DomainProperties (Export DomainModule : DomainSignature).

Add Morphism e with signature E ==> E ==> eq_bool as e_wd.
Proof.
intros x x' Exx' y y' Eyy'.
case_eq (e x y); case_eq (e x' y'); intros H1 H2; trivial.
assert (x == y); [apply <- E_equiv_e; now rewrite H2 |
assert (x' == y'); [rewrite <- Exx'; now rewrite <- Eyy' |
rewrite <- H1; assert (H3 : e x' y'); [now apply -> E_equiv_e | now inversion H3]]].
assert (x' == y'); [apply <- E_equiv_e; now rewrite H1 |
assert (x == y); [rewrite Exx'; now rewrite Eyy' |
rewrite <- H2; assert (H3 : e x y); [now apply -> E_equiv_e | now inversion H3]]].
Qed.

Theorem neq_symm : forall n m, n # m -> m # n.
Proof.
intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

End DomainProperties.
