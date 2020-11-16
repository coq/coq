Class C (n: nat) := T{x:True}.
Generalizable All Variables.

Fail Instance i : C n.

Instance i : `(C n).
Proof. repeat constructor. Defined.
