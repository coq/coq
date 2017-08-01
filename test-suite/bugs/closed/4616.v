Require Coq.extraction.Extraction.

Set Primitive Projections.
Record Foo' := Foo { foo : Type }.
Definition f := forall t : Foo', foo t.
Extraction f.
Extraction TestCompile f.
