Variable Ack : nat -> nat -> nat.

Axiom Ack0 : forall m : nat, Ack 0 m = S m.
Axiom Ack1 : forall n : nat, Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall n m : nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

Hint Rewrite Ack0 Ack1 Ack2 : base0.

Lemma ResAck2 : forall H:(Ack 2 2 = 7 -> False), H=H  -> False.
Proof.
  intros.
  Fail autorewrite with base0 in * using try (apply H1;reflexivity).



