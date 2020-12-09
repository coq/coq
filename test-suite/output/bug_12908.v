Definition mult' m n := 2 * m * n.

Module A.
(* Test hiding of a scoped notation by a lonely notation *)
Infix "*" := mult'.
Check forall m n, mult' m n = Nat.mul (Nat.mul 2 m) n.
End A.

Module B.
(* Test that an overridden scoped notation is deactivated *)
Infix "*" := mult' : nat_scope.
Check forall m n, mult' m n = Nat.mul (Nat.mul 2 m) n.
End B.
