Set Universe Polymorphism.
Module Type FOO.
  Parameter f : Type -> Type.
  Parameter h : forall T, f T.
End FOO.

Module Type BAR.
  Include FOO.
End BAR.

Module Type BAZ.
  Include FOO.
End BAZ.

Module BAR_FROM_BAZ (baz : BAZ) <: BAR.

  Definition f : Type -> Type. 
  Proof. exact baz.f. Defined.

  Definition h : forall T, f T.
  Admitted.

Fail End BAR_FROM_BAZ.
