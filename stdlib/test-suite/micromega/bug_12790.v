From Stdlib Require Import Lia.

Goal forall (a b c d x: nat),
S c = a - b -> x <= x + (S c) * d.
Proof.
intros a b c d x H.
lia.
Qed.
