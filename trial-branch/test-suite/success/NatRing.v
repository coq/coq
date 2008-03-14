Require Import ArithRing.

Lemma l1 : 2 = 1 + 1.
ring.
Qed.

Lemma l2 : forall x : nat, S (S x) = 1 + S x.
intro.
ring.
Qed.
