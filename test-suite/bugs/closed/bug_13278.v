Inductive even: nat -> Prop :=
| evenB: even 0
| evenS: forall n, even n -> even (S (S n)).

Goal even 1 -> False.
Proof.
  refine (fun a => match a with end).
Qed.
