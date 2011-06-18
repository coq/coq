Variable Ack : nat -> nat -> nat.

Axiom Ack0 : forall m : nat, Ack 0 m = S m.
Axiom Ack1 : forall n : nat, Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall n m : nat, Ack (S n) (S m) = Ack n (Ack (S n) m).

Hint Rewrite Ack0 Ack1 Ack2 : base0.

Lemma ResAck0 : (Ack 2 2 = 7 -> False) -> False.
Proof.
  intros.
  autorewrite with base0 in H using try (apply H; reflexivity).
Qed.

Lemma ResAck1 : forall H:(Ack 2 2 = 7 -> False), True -> False.
Proof.
  intros.
  autorewrite with base0 in *.
    apply H;reflexivity.
Qed.

(* Check autorewrite does not solve existing evars *)
(* See discussion started by A. Chargueraud in Oct 2010 on coqdev *)

Hint Rewrite <- plus_n_O : base1.
Goal forall y, exists x, y+x = y.
eexists. autorewrite with base1.
Fail reflexivity.

