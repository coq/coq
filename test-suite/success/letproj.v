Set Primitive Projections.
Set Record Elimination Schemes.
Record Foo (A : Type) := { bar : A -> A; baz : A }.

Definition test (A : Type) (f : Foo A) :=
  let (x, y) := f in x.

Scheme foo_case := Case for Foo Sort Type.

