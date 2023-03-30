Inductive free := Par (A1:Type).

Lemma foo
  (A0 : Type@{free.u0})
  A1
  (H1 : Par A0 = Par A1)
  : A0 = A1.
Proof.
  congruence.
Qed.
