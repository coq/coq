Section Foo.
  Variable A : Type.

  Definition bla := A.

  Variable B : bla.

  Lemma blu : {X:Type & X}.
  Proof using A B.
    exists bla;exact B.
  Qed.
End Foo.
