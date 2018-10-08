Require Coq.extraction.Extraction.

Set Primitive Projections.
Record Foo' := Foo { foo : nat }.
Extraction foo.
Record Foo2 (a : nat) := Foo2c { foo2p : nat; foo2b : bool }.
Extraction foo2p.

Definition bla (x : Foo2 0) := foo2p _ x.
Extraction bla.

Definition bla' (a : nat) (x : Foo2 a) := foo2b _ x.
Extraction bla'.

Extraction TestCompile foo foo2p bla bla'.
