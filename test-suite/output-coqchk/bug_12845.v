Module Type A.
  Module B.
    Axiom t : Set.
  End B.
End A.

Module a : A.
  Module B.
    Definition t : Set := unit.
  End B.
End a.

Check a.B.t.
