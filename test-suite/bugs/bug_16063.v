Parameter t : bool -> Type.
Parameter f : forall (b : bool), t b.
Arguments f &.
Fail Definition v : t false := f true.

(* Anomaly "Uncaught exception Evarconv.UnableToUnify(_, _)." *)
