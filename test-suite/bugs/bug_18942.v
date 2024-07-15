Lemma foo: True /\ True.
Proof.
  split. admit.
  abstract exact I. (* (in proof foo_subproof): Attempt to save a proof with given up goals. *)
Fail Qed.
Abort.
