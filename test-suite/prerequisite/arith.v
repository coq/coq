Axiom eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.

Module Nat.
Axiom add_0_l : forall n : nat, 0 + n = n.
Axiom add_0_r : forall n : nat, n + 0 = n.
Axiom nlt_0_r : forall n : nat, ~ n < 0.
Axiom succ_lt_mono : forall n m : nat, n < m <-> S n < S m.
Axiom lt_lt_succ_r : forall n m : nat, n < m -> n < S m.
End Nat.
