(* Check static globalisation of tactic names *)
(* Proposed by Benjamin (mars 2002) *)
Goal forall n : nat, n = n.
induction n.
Fail try REflexivity.

