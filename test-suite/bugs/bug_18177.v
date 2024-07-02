From Coq Require Import PeanoNat.

Arguments Nat.succ_lt_mono {n m}.

Lemma bar (n m : nat) : n < m -> S n < S m.
Proof.
  intros H.
  now apply -> Nat.succ_lt_mono.
Qed.
