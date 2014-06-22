Class A := a : nat.
Lemma p : True.
Proof. cut A; [tauto | exact 1]. Qed.
