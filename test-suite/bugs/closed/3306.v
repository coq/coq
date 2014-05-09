
Inductive Foo(A : Type) : Prop :=
  foo: A -> Foo A.

Arguments foo [A] _.

Scheme Foo_elim := Induction for Foo Sort Prop.

Goal forall (fn : Foo nat), { x: nat | foo x = fn }.
intro fn.
Fail induction fn as [n] using Foo_elim. (* should fail in a non-Prop context *)
Admitted. 
