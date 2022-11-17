Module Outer.
  Module Simple.
    Definition t := nat.
  End Simple.
  Module Contain.
    Include Simple.
  End Contain.
  Module E.
  End E.
  Module Def := E.
End Outer.

Include Outer.
Search Nat.add.
(* Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/. *)
