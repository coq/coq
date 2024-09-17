Definition id@{i} (A : Type@{i}) (a : A) := a.

Set Debug "loop-checking-set".
Set Universe Polymorphism.
Class Foo@{i} (A : Type@{i}) := { foo : A }.

Instance foo_nat : Foo@{Set} nat.
Proof. exact {| foo := O |}. Defined.

Goal True.
Proof.
  eassert (f : Foo nat).
  Show Universes.
  apply foo_nat.
  Show Universes.
  exact I.
Qed.
