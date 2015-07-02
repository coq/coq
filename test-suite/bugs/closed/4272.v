Set Implicit Arguments.

Record foo := Foo { p1 : Type; p2 : p1 }.

Variable x : foo.

Let p := match x with @Foo a b => a end.

Notation "@ 'id'"  := 3 (at level 10).
Notation "@ 'sval'" := 3 (at level 10).

Let q := match x with @Foo a b => a end.
