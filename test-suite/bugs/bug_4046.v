Module Import Foo.
  Class Foo := { foo : Type }.
End Foo.

#[export] Instance f : Foo := { foo := nat }. (* works fine *)
#[export] Instance f' : Foo.Foo := { Foo.foo := nat }.
