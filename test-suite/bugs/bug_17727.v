Universes u v.
Constraint u < v.

Section S.
  Variable T : Type@{u}.

  Lemma foo : True.
  Proof.
    clear T.
    assert (T : Type@{v}) by exact nat.
    abstract exact I.
  Qed.
End S.
