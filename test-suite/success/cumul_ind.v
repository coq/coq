Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Definition rel (A : Type) := A -> A -> Prop.

Inductive test (K : Type) :=
| Test : Type -> test K.

(* The transparent alias [rel] should behave like the unfolded arity
   [test K -> test K -> Prop]. *)
(* Cumulativity Transparent rel. *)
Set Printing Universes.
Print test.
Inductive test_rel (K : Type) : rel (test K) := .
Print test_rel.
Inductive test_rel'@{u u0} (K : Type@{u}) : rel@{u0+1} (test@{u u0} K) := .
