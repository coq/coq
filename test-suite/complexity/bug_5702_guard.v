(* Examples of strong guard condition failures not requiring backtracking *)
(* Expected time < 1.00s *)

Fixpoint f (n : nat) {struct n} : nat.
Proof.
  do 21 (refine (id _)).
  exact (f n).
Timeout 5 Time Fail Defined. (* Slow. *)
Abort.

Fixpoint f (n m : nat) : nat.
Proof.
  do 20 (refine (id _)).
  destruct m.
  - exact O.
  - exact (f n m).
Timeout 5 Time Defined. (* Slow. *)
