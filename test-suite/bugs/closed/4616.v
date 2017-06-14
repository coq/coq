Require Coq.extraction.Extraction.

Set Primitive Projections.
Record Foo' := Foo { foo : Type }.
Axiom f : forall t : Foo', foo t.
Extraction f.
