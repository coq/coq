Require Import Setoid Ring Ring_theory.

Module abs_ring.

Parameters (Coef:Set)(c0 c1 : Coef)
(cadd cmul csub: Coef -> Coef -> Coef)
(copp : Coef -> Coef)
(ceq : Coef -> Coef -> Prop)
(ceq_sym : forall x y, ceq x y -> ceq y x)
(ceq_trans : forall x y z, ceq x y -> ceq y z -> ceq x z)
(ceq_refl : forall x, ceq x x).


Add Relation Coef ceq
  reflexivity proved by ceq_refl symmetry proved by ceq_sym
  transitivity proved by ceq_trans
  as ceq_relation.

Add Morphism cadd with signature ceq ==> ceq ==> ceq as cadd_Morphism.
Admitted.

Add Morphism cmul with signature ceq ==> ceq ==> ceq as cmul_Morphism.
Admitted.

Add Morphism copp with signature ceq ==> ceq as copp_Morphism.
Admitted.

Definition cRth : ring_theory c0 c1 cadd cmul csub copp ceq.
Admitted.

Add Ring CoefRing : cRth.

End abs_ring.
Import abs_ring.

Theorem check_setoid_ring_modules :
  forall a b, ceq (cadd a b) (cadd b a).
intros.
ring.
Qed.
