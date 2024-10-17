From Stdlib Require Import Psatz.

Inductive TT : Set :=
| C : nat -> TT.

Lemma lem4 : forall (n m : nat),
S m <= m -> C (S m) <> C n -> False.
Proof. firstorder lia. Qed.

Print Assumptions lem4.
