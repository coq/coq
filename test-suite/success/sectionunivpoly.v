
Unset Universe Polymorphism.
Section Foo.
  Variable A : Type.

  Section Bar.
    Set Universe Polymorphism.
    Fail Variable A : Type.
    Fail Universe i.
    Fail Definition foo := A -> Type.
  End Bar.
End Foo.
