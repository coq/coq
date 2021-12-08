Parameter a b : nat.
Parameter p : a = b.

Goal exists (_ : True) (_ : exists x, x = b), True.
Proof.
  exists I, (ex_intro _ a p).
  exact I.
Qed.
