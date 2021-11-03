
Module Import Foo_DOT_A.
  Module Foo.
    Module A.
      Axiom a : Set.
    End A.
  End Foo.
End Foo_DOT_A.

Module Foo.
  Import Foo.A.
  Module A.
    Axiom b : Prop.
    Import Foo.A.
    Locate Foo.A.
  End A.
  Section A.
    Import Foo.A.
    Locate Foo.A.
  End A.
End Foo.
