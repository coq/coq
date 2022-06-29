Require Import Classes.CMorphisms Classes.CRelationClasses.
Require Setoids.Setoid.

Axiom Equiv : Type -> Type -> Type.

#[export] Instance equivalence_equiv : CRelationClasses.Equivalence Equiv.
Admitted.

#[export] Instance prod_equiv : CMorphisms.Proper (Equiv ==> Equiv ==> Equiv) prod.
Admitted.

Lemma foo {A B C:Type} (X: Equiv A B) : Equiv (prod C A) (prod C B).
Proof.
  setoid_rewrite X.
  reflexivity.
Qed.
