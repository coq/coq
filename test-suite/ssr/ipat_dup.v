Require Import ssreflect.

Section Dup.

Variable P : nat -> Prop.

Lemma test_dup1 : forall n : nat, P n.
Proof. move=> /[dup] m n; suff: P n by []. Abort.

Lemma test_dup2 : let n := 1 in False.
Proof. move=> /[dup] m n; have : m = n := eq_refl. Abort.

End Dup.
