Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Record category (A : Type) :=
  { ob :> Type;
    hom : ob -> ob -> Type
  }.

Record foo { A: Type } := { C : category A; x : ob C; y :> hom _ x x }.
Definition comp A (C : category A) (x : C) (f : hom _ x x) := f.

Definition bar A (f : @foo A) := @comp _ _ _ f.

(* Toplevel input, characters 0-42:
Error: Cannot find the target class. *)
