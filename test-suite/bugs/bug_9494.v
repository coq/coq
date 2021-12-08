Lemma foo (a : nat) : True.
Proof.
destruct a eqn:n; exact I.
Qed.

Set Mangle Names.
Lemma foo2 (a : nat) : True.
Proof.
let N := fresh in destruct a eqn:N; exact I.
Qed.
