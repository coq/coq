Module Type S.
Parameter t : Type.
End S.

Module Bar(X : S).
Definition elt := X.t.
Axiom fold : elt.
End Bar.

Module Make (Z: S) := Bar(Z).

Declare Module Y : S.

Module Type Interface.
Parameter constant : unit.
End Interface.

Module DepMap : Interface.
Module Dom := Make(Y).
Definition constant : unit :=
  let _ := @Dom.fold in tt.
End DepMap.

Print Assumptions DepMap.constant.
