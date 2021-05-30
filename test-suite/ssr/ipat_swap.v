Require Import ssreflect.

Section Swap.

Definition P n := match n with 1 => true | _ => false end.

Lemma test_swap1 : forall (n : nat) (b : bool), P n = b.
Proof. move=> /[swap] b n; suff: P n = b by []. Abort.

Lemma test_swap2 : let n := 1 in let b := true in False.
Proof. move=> /[swap] b n; have : P n = b := eq_refl. Abort.

Lemma test_swap_plus P Q R : P -> Q -> R -> False.
Proof.
move=> + /[swap].
suff: P -> R -> Q -> False by [].
Abort.

Lemma test_swap_plus2 P : P -> let x := 0 in let y := 1 in False.
Proof.
move=> + /[swap].
suff: P -> let y := 1 in let x := 0 in False by [].
Abort.

End Swap.
