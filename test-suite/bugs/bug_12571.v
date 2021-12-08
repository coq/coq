Axiom IsTrunc : Type -> Type.

Existing Class IsTrunc.

Declare Instance trunc_forall :
  forall (A : Type) (P : A -> Type),
  IsTrunc (forall a : A, P a).

Axiom Graph : Set.
Axiom in_N : forall (n : Graph), Type.

Definition N : Type := @sigT Graph in_N.

Goal forall (P : N -> Type)
 (Q := fun m : Graph => forall mrec : in_N m, P (existT _ m mrec))
 (A : Graph), IsTrunc (Q A).
Proof.
intros.
solve [typeclasses eauto].
Qed.
