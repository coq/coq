Require Import ssreflect.

Section Dup.

Section withP.

Variable P : nat -> Prop.

Lemma test_dup1 : forall n : nat, P n.
Proof. move=> /[dup] m n; suff: P n by []. Abort.

Lemma test_dup2 : let n := 1 in False.
Proof. move=> /[dup] m n; have : m = n := eq_refl. Abort.

End withP.

Lemma test_dup_plus P Q : P -> Q -> False.
Proof.
move=> + /[dup] q.
suff: P -> Q -> False by [].
Abort.

Lemma test_dup_plus2 P : P -> let x := 0 in False.
Proof.
move=> + /[dup] y.
suff: P -> let x := 0 in False by [].
Abort.

End Dup.
