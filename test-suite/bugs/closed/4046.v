Module Import Foo.
  Class Foo := { foo : Type }.
End Foo.

Instance f : Foo := { foo := nat }. (* works fine *)
Instance f' : Foo.Foo := { Foo.foo := nat }. 
