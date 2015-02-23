(* Test smooth failure on not fully applied term to destruct with eqn: given *)
Goal True.
Fail induction S eqn:H.
