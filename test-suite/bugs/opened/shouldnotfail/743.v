Require Import Omega.

Lemma foo : forall n m : Z, (n >= 0)%Z -> (n * m >= 0)%Z -> (n <= n + n * m)%Z.
Proof.
  intros. omega.
Qed.

Lemma foo' : forall n m : nat, n <=  n + n * m.
Proof.
  intros. Fail omega.
Abort.

