Universes u v.

Constraint u < v.

(* also happens with Module Type *)
Module Off.
  Local Unset Universe Checking.
  Succeed Constraint v < u.
End Off.

Fail Constraint v < u.
