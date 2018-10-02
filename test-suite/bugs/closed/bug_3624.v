Set Implicit Arguments.
Module NonPrim.
  Class foo (m : Set) := { pf : m = m }.
  Notation pf' m := (pf (m := m)).
End NonPrim.

Module Prim.
  Set Primitive Projections.
  Class foo (m : Set) := { pf : m = m }.
  Notation pf' m := (pf (m:=m)). (* Wrong argument name: m. *)
End Prim.
