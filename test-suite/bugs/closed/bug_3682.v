Require Import TestSuite.admit.
Class Foo.
Definition bar `{Foo} (x : Set) := Set.
Instance: Foo.
Definition bar1 := bar nat.
Definition bar2 := bar ltac:(admit).
