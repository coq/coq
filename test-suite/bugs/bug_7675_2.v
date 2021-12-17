Require Import Setoid CMorphisms.

Parameter A : Type.
Parameter R : A -> A -> Type.

Inductive P : A -> Type := c1 : forall a, P a | c2 : forall a, P a.
(* requires at least two constructors for the issue to appear *)
#[local] Instance P_R : Proper (R ==> arrow) P. Admitted.

Goal forall a b, R a b -> P a -> P b.
Proof.
intros a b HR HP.
Succeed rewrite HR in HP.
Succeed rewrite <- HR.
apply (P_R _ _ HR HP).
Qed.
