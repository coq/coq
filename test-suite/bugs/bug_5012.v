Class Foo := { foo : Set }.

Axiom admit : forall {T}, T.

Global Instance Foo0 : Foo
  := {| foo := admit |}.

Global Instance Foo1 : Foo
  := { foo := admit }.

Existing Class Foo.

Global Instance Foo2 : Foo
  := { foo := admit }. (* Error: Unbound method name foo of class Foo. *)

Set Warnings "+already-existing-class".
Fail Existing Class Foo.
