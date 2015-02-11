Module Type S.
End S.

Module F (E : S).

  Tactic Notation "foo" := idtac.

  Ltac bar := foo.

End F.

Module G (E : S).
  Module M := F E.

  Lemma Foo : True.
  Proof.
  M.bar.
  Abort.

End G.
