Module NonPrim.
  Class AClass := { x : Set }.
  Arguments x {AClass}.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Class AClass := { x : Set }.
  Arguments x {AClass}.
End Prim.
