Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Record category :=
  { ob :> Type;
    hom : ob -> ob -> Type
  }.

Fail Record foo := { C : category; x :> ob C }.
(* Toplevel input, characters 0-42:
Error: Cannot find the target class. *)
