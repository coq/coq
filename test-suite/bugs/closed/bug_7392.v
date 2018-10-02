Inductive R : nat -> Prop := ER : forall n, R n -> R (S n).

Goal (forall (n : nat), R n -> False) -> True -> False.
Proof.
intros H0 H1.
eapply H0.
clear H1.
apply ER.
simpl.
