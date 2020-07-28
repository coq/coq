(** Check for error message when missing a record field. Error message
should contain missing field, and the inferred type of the record **)

Record point2d := mkPoint { x2p: nat; y2p: nat }.

Fail Definition increment_x (p: point2d) : point2d :=
  {| x2p := x2p p + 1; |}.

(* Here there is also an unresolved implicit, which should give an
   understadable error as well *)
Fail Definition increment_x (p: point2d) : point2d :=
  {| x2p := x2p p + (fun n => _) 1; |}.
