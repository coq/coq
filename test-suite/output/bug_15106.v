Require Import Coq.Program.Tactics.
Obligation Tactic := try constructor.
Program Definition foo := (fun (x : False) (y : True) => I) _ _.
Obligation 2.
