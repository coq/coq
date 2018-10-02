Module Type A .
 Tactic Notation "bar" := idtac "ITSME".
End A.

Module Type B.
 Tactic Notation "foo" := fail "NOTME".
End B.

Module Type C := A <+ B.

Module Type F (Import M : C).

Lemma foo : True.
Proof.
bar.
