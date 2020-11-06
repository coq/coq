Require Import ssreflect.

Section Swap.

Variable P : nat -> bool.

Lemma test_swap1 : forall (n : nat) (b : bool), P n = b.
Proof. move=> /[swap] b n; suff: P n = b by []. Abort.

Lemma test_swap1 : let n := 1 in let b := true in False.
Proof. move=> /[swap] b n; have : P n = b := eq_refl. Abort.

End Swap.
