Unset Strict Universe Declaration.
Set Universe Polymorphism.

Module Type Foo.
  Definition U := Type : Type.
  Parameter eq : Type = U.
End Foo.

Module M : Foo with Definition U := Type : Type.
  Definition U := let X := Type in Type.
  Definition eq : Type = U := eq_refl.
Fail End M.
