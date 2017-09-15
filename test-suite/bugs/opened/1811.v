Require Export Bool.

Lemma neg2xor : forall b, xorb true b = negb b.
Proof. auto. Qed.

Goal forall b1 b2, (negb b1 = b2)  ->  xorb true b1 = b2.
Proof.
  intros b1 b2.
  Fail rewrite neg2xor.
Abort.
