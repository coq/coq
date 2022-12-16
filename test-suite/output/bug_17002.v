
Module Eq.
  Universes u v.
  Constraint u = v.

  (* we test both directions to be invariant wrt which universe got picked as canonical *)
  Fail Constraint u < v.
  Fail Constraint v < u.
End Eq.

Module Lt.
  Universes u v.
  Constraint u < v.

  Fail Constraint u = v.
  Fail Constraint v = u.
End Lt.
