Class Foo.
Definition bar `{Foo} (x : Set) := Set.
Instance: Foo.
Definition bar1 := bar nat.
Fail Definition bar2 := bar $(admit)$.
