Require Import Classes.CMorphisms Classes.CRelationClasses.
Require Setoids.Setoid.

Axiom Equiv : Type -> Type -> Type.

Instance equivalence_equiv : CRelationClasses.Equivalence Equiv.
Admitted.

Instance prod_equiv : CMorphisms.Proper (Equiv ==> Equiv ==> Equiv) prod.
Admitted.

Goal forall {A B C:Type}, Equiv A B -> Equiv (prod C A) (prod C B).
  intros.
  setoid_rewrite X.
  now eapply prod_equiv.
Qed.
