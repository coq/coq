Axiom var term : Type.

Fail Inductive Foo : list var -> term -> Prop :=
| foo : forall l x, Foo (cons x l) x.
