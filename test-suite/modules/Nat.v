Definition T := nat.

Definition le := le.

Hint Unfold le.

Lemma le_refl : forall n : nat, le n n.
  auto.
Qed.

Require Import Le.

Lemma le_trans : forall n m k : nat, le n m -> le m k -> le n k.
   eauto with arith.
Qed.

Lemma le_antis : forall n m : nat, le n m -> le m n -> n = m.
   eauto with arith.
Qed.
