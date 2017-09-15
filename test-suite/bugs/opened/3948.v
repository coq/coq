Module Type S.
Parameter t : Type.
End S.

Module Bar(X : S).
Proof.
  Definition elt := X.t.
  Axiom fold : elt.
End Bar.

Module Make (X: S) := Bar(X).

Declare Module X : S.

Module Type Interface.
  Parameter constant : unit.
End Interface.

Module DepMap : Interface.
  Module Dom := Make(X).
  Definition constant : unit :=
    let _ := @Dom.fold in tt.
End DepMap.

Print Assumptions DepMap.constant.
