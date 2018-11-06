Require Import ssreflect.
Goal True \/ True -> False.
Proof.
(* the following should fail: 2 subgoals, but only one intro pattern *)
Fail case => [a].
Abort.
