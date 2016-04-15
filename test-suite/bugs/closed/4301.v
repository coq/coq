Unset Strict Universe Declaration.
Set Universe Polymorphism.

Module Type Foo.
  Parameter U : Type.
End Foo.

Module Lower (X : Foo with Definition U := True : Type).
End Lower.

Module M : Foo.
  Definition U := nat : Type@{i}. 
End M.
