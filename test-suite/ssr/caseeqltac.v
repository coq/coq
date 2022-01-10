Require Import ssreflect.

Goal (1 + 2 = 3).
Proof.
let E := fresh "F" in
move E: (2 in LHS) => n.
rewrite F.
by [].
Qed.
