Inductive foo (V:Type):Type :=
  | Foo : list (bar V) -> foo V
with bar (V:Type): Type :=
  | bar1: bar V
  | bar2 : V -> bar V.

Module WithPoly.
Polymorphic Inductive foo (V:Type):Type :=
  | Foo : list (bar V) -> foo V
with bar (V:Type): Type :=
  | bar1: bar V
  | bar2 : V -> bar V.
End WithPoly.
