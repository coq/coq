Goal True.
Proof.
pose (T := forall A, A).
native_compute in T.
(* Anomaly "the kernel does not support sort variables" *)
Abort.
