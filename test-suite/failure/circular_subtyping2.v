(* Circular substitution check at functor application *)
Module Type S. End S.
Module Type T. Declare Module M:S. End T.
Module N:S. End N.

Module F (X:S) (Y:T with Module M:=X). End F.
Module A := F N N.

(* Circular substitution check at with definition *)
(* Should it be implemented?? *)
(*

Module NN:T. Module M:=N. End NN.
Module Type U := T with Module M:=NN.
(*
User error: The construction "with Module M:=..." is about to create
a circular module type. Their resolution is not implemented yet.
If you really need that feature, please report.
*)
*)
