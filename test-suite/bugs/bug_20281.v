Axiom Q : Prop.

Goal forall (A : Type) (P : A -> Prop) (X : A) (H : forall b : A, and Q (P b)), Q.
Proof.
intros.
solve [firstorder].
Qed.
