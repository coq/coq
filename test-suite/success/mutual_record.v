Module M0.

Inductive foo (A : Type) := Foo {
  foo0 : option (bar A);
  foo1 : nat;
  foo2 := foo1 = 0;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := 0;
  bar2 : bar1 = 0;
  bar3 : nat -> foo A;
}.

End M0.

Module M1.

Set Primitive Projections.

Inductive foo (A : Type) := Foo {
  foo0 : option (bar A);
  foo1 : nat;
  foo2 := foo1 = 0;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := 0;
  bar2 : bar1 = 0;
  bar3 : nat -> foo A;
}.

End M1.

Module M2.

Set Primitive Projections.

CoInductive foo (A : Type) := Foo {
  foo0 : option (bar A);
  foo1 : nat;
  foo2 := foo1 = 0;
  foo3 : foo2;
}

with bar (A : Type) := Bar {
  bar0 : A;
  bar1 := 0;
  bar2 : bar1 = 0;
  bar3 : nat -> foo A;
}.

End M2.
