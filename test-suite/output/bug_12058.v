Set Universe Polymorphism.

Module FooBar.
  Definition foo@{u} (A : Type@{u}) : A -> A := fun a => a.
End FooBar.

Set Printing Universes.
Print FooBar.
(* Module *)
(* FooBar *)
(* := Struct *)
(*      Definition foo : forall A : Type@{Top.51}, A -> A. *)
(*        (* Top.51 |=  *) *)
(*    End *)

Print FooBar.foo.
(* FooBar.foo@{u} =  *)
(* fun (A : Type@{u}) (a : A) => a *)
(*      : forall A : Type@{u}, A -> A *)
(* (* u |=  *) *)
(* FooBar.foo is universe polymorphic *)
(* Argument scopes are [type_scope _] *)
