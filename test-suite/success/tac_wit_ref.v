Tactic Notation "foo" reference(n) := idtac n.

Goal forall n : nat, n = 0.
Proof.
intros n.
foo nat.
foo n.
Abort.
