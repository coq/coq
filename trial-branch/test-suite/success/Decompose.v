(* This was a Decompose bug reported by Randy Pollack (29 Mar 2000) *)

Goal
0 = 0 /\ (forall x : nat, x = x -> x = x /\ (forall y : nat, y = y -> y = y)) ->
True.
intro H.
decompose [and] H. (* Was failing *)

Abort.
