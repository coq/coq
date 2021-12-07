Goal True.
Proof.
refine (id _).
Optimize Proof.
Guarded.
Abort.
(* Anomaly "Uncaught exception Constr.DestKO."
Please report at http://coq.inria.fr/bugs/. *)
