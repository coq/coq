Set Universe Polymorphism.

Module Type Foo.
  Definition U := Type.
End Foo.

Fail Module M : Foo with Definition U := Prop.
