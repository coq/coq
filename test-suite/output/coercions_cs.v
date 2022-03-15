Set Warnings "-uniform-inheritance".
Set Printing All.

Module CS.

Structure foo := { sort :> Type; a : sort }.

Axiom T1 : Type -> Type.
Axiom T2 : Type -> Type.
Axiom x : T1 nat.

Module T1.
Axiom f : forall A : foo, T1 (sort A) -> T2 nat.
#[canonical] Definition foo_nat := {| sort := nat; a := 1 |}.
Coercion f : T1 >-> T2.
Check (x : T2 _).
End T1.

Module T2.
Axiom f : forall A : foo, T1 (sort A) -> T2 nat.
#[canonical] Definition foo_A A x := {| sort := A; a := x |}.
Coercion f : T1 >-> T2.
Check (f _ x : T2 _).
End T2.

End CS.
