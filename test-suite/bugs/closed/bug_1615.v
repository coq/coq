Require Export ZArith_base.
Require Import Lia.

Lemma foo (n m : Z) : (n >= 0)%Z -> (n * m >= 0)%Z -> (n <= n + n * m)%Z.
Proof. now lia. Qed.

Lemma foo' : forall n m : nat, n <=  n + n * m.
Proof. now lia. Qed.
