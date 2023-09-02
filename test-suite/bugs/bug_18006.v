Lemma foo : nat -> nat.
Proof.
  fix f 1.
  intros n.
  epose (fun a:nat => _).
  exact (f n).
  Fail Guarded.
Abort.
