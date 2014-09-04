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

Set Primitive Projections.
Unset Elimination Schemes.
Set Implicit Arguments.

Check nat.

(* Inductive X (U:Type) := Foo (k : nat) (x : X U).  *)
(* Parameter x : X nat. *)
(* Check x.(k). *)

Inductive X (U:Type) := { k : nat; a: k = k -> X U; b : let x := a eq_refl in X U }.

Parameter x:X nat.
Check (a x : forall _ : @eq nat (k x) (k x), X nat).
Check (b x : X nat).

Inductive Y := { next : option Y }.

Check _.(next) : option Y.
Lemma eta_ind (y : Y) : y = Build_Y y.(next).
Proof. reflexivity. Defined.

Variable t : Y.

Fixpoint yn (n : nat) (y : Y) : Y := 
  match n with
    | 0 => t
    | S n => {| next := Some (yn n y) |}
  end.

Lemma eta_ind'  (y: Y) : Some (yn 100 y) = Some {| next := (yn 100 y).(next) |}.
Proof. reflexivity. Defined.
