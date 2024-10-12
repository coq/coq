From Stdlib Require Export Lia.
Set Mangle Names.
Lemma test (n : nat) : n <= 10 -> n <= 20.
Proof. lia. Qed.

Lemma test2 : 0 < 1.
Proof. lia. Qed.
