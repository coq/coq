(* Check keywords Conjecture and Admitted are recognized *)

Conjecture c : forall n : nat, n = 0.

Check c.

Theorem d : forall n : nat, n = 0.
Proof.
  induction n.
  reflexivity.
  assert (H : False).
  2: destruct H.
Admitted.
