Axiom var term : Type.

Inductive Foo : list var -> term -> Prop :=
| foo : forall l x, Foo (cons x l) x.
