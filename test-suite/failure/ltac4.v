(* Check static globalisation of tactic names *)
(* Proposed by Benjamin (mars 2002) *)
Goal (n:nat)n=n.
Induction n; Try REflexivity.
