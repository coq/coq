Class Funext := {}.

Axioms A B : Type.
Axiom f : forall {_ : Funext}, A -> B.
Coercion f : A >-> B.

Definition f' {_ : Funext} (a : A) : B := a.
