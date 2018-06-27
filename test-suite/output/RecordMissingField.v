(** Check for error message when missing a record field. Error message
should contain missing field, and the inferred type of the record **)

Record point2d := mkPoint { x2p: nat; y2p: nat }.


Definition increment_x (p: point2d) : point2d :=
  {| x2p := x2p p + 1; |}.
