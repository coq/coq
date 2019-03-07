Class Foo (A : Type) := { foo_a : A }.
Hint Mode Foo ! : typeclass_instances.
Definition foo_dependent {A} {F : Foo A} (x : A) : True := I.
Set Printing All.
Instance: Foo nat := { foo_a := 0 }.
Goal False.
  Fail refine (foo_dependent 1).
Abort.
