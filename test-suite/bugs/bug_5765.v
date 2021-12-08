(* 'pat binder not (yet?) allowed in parameters of inductive types *)

Fail Inductive X '(a,b) := x.
