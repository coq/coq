
Module Type E. Parameter T : Type. End E.

Module F (X:E).
  Inductive foo := box : X.T -> foo.
End F.

Module ME. Definition T := nat. End ME.
Module A := F ME.
(* Note: A.foo could live in Set, and coqchk sees that (because of
   template polymorphism implementation details) *)
