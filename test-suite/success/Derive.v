Require Import Derive.

Derive foo : nat SuchThat (foo = foo) As bar.
Proof.
reflexivity.
Unshelve.
exact 0.
Qed.
