Set Primitive Projections.
Set Record Elimination Schemes.
Module Prim.

Record F := { a : nat; b : a = a }.
Record G (A : Type) := { c : A; d : F }.

Check c.
End Prim.
Module Univ.
Set Universe Polymorphism.
Set Implicit Arguments.
Record Foo (A : Type) := { foo : A }.

Record G (A : Type) := { c : A; d : c = c; e : Foo A }.

Definition Foon : Foo nat := {| foo := 0 |}.

Definition Foonp : nat := Foon.(foo).

Definition Gt : G nat := {| c:= 0; d:=eq_refl; e:= Foon |}.

Check (Gt.(e)).

Section bla.

  Record bar := { baz : nat; def := 0; baz' : forall x, x = baz \/ x = def }.
End bla.

End Univ.
