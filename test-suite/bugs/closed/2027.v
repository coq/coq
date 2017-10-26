
Parameter T : Type -> Type.
Parameter f : forall {A}, T A -> T A.
Parameter P : forall {A}, T A -> Prop.
Axiom f_id : forall {A} (l : T A), f l = l.

Goal forall A (p : T A), P p.
Proof.
  intros.
  rewrite <- f_id.
Admitted.
