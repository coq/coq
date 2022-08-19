Set Fast Name Printing.

Lemma le_succ_diag_r (n : nat) : n <= S n.
Proof.
  apply (nat_ind (fun p : nat => p <= S n)).
  apply le_0_n.
  Show.
Abort.
