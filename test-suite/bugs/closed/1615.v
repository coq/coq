Require Import ZArith Lia.

Lemma foo : forall n m : Z, (n >= 0)%Z -> (n * m >= 0)%Z -> (n <= n + n * m)%Z.
Proof.
  intros. lia.
Qed.

Lemma foo' : forall n m : nat, n <=  n + n * m.
Proof.
  intros. lia.
Qed.
