Require Import Lia.

Axiom P : nat -> Set.

Goal forall n : nat, n < 0 -> P n.
intros. lia.
Qed.
