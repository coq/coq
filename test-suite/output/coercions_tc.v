Set Warnings "-uniform-inheritance".
Set Printing All.

Module TC.

Class foo (A : Type) := { a : A }.
#[local] Hint Mode foo + : typeclass_instances.

#[local] Instance bool_foo : foo bool := {| a := true |}.
#[local] Instance nat_foo : foo nat := {| a := 1 |}.
#[local] Instance pair_foo A B : foo A -> foo B -> foo (A * B) := fun x y => {| a := (a,a) |}.

Axiom T1 : Type -> Type.
Axiom T2 : Type -> Type.
Axiom x : T1 nat.

Module T1.
Axiom f : forall A, foo (A * bool) -> T1 A -> T2 nat.
Coercion f : T1 >-> T2.
Check (x : T2 _).
End T1.

Module T2.
Axiom f : forall A, foo A -> T1 nat -> T2 A.
Coercion f : T1 >-> T2.
Check (x : T2 _).
Check (x : T2 bool).
End T2.

End TC.
