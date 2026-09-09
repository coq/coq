Module Type T. Parameter l : bool. End T.
Module F (X : T). Module Sub := X. End F.
Module N.
Definition l := true.
Include F.      (* Include Self: X := N, so N.Sub is an alias of N *)
Fail Include Sub.    (* including a module that aliases the includer *)
(* Anomaly "File "kernel/mod_subst.ml", line 258, characters 11-17: Assertion failed." *)
End N.
