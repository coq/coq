Module Type FOO.
  Parameters P Q : Type -> Type.
End FOO.

Module Type BAR.
  Declare Module Import foo : FOO.
  Parameter f : forall A, P A -> Q A -> A.
End BAR.

Module Type BAZ.
  Declare Module Export foo : FOO.
  Parameter g : forall A, P A -> Q A -> A.
End BAZ.

Module BAR_FROM_BAZ (baz : BAZ) : BAR.
  Import baz.
  Module foo <: FOO := foo.
  Import foo.
  Definition f : forall A, P A -> Q A -> A := g.
End BAR_FROM_BAZ.
