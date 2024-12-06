Require Import Corelib.Program.Tactics.
Local Obligation Tactic := try constructor.

Axiom P : Prop. Axiom p : P.

Program Definition foo := (fun (x : P) (y : True) => I) _ _.
Fail Obligation 2.

Obligation 1. exact p. Qed.
