Notation succn := (Datatypes.S).

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.

Locate ".+1".
(* Notation *)
(* "n .+1" := S n : nat_scope (default interpretation) *)
(** so Coq does not apply succn notation *)

Check forall x : nat, x.+1 = x.+1.
