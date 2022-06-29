Class C (n: nat) := T{x:True}.
Generalizable All Variables.

Fail #[export] Instance i : C n.

#[export] Instance i : `(C n).
Proof. repeat constructor. Defined.
