From Stdlib Require Import PeanoNat Lia.

Goal forall x, Nat.le x x.
Proof.
intros.
lia.
Qed.

Goal forall x, Nat.lt x x -> False.
Proof.
intros.
lia.
Qed.

Goal forall x, Nat.eq x x.
Proof.
intros.
lia.
Qed.
