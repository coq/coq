Require Extraction.

Definition f := 0.
Module M.
  Recursive Extraction f.
  Extraction f.

  Definition g := f.
  Recursive Extraction g.
  Extraction g.

  Module Type S. Definition b := 0. End S.

  (* Test with sealed module *)
  Module N : S.
    Definition b := 0.
    Definition h := g.
    Recursive Extraction h.
    Extraction h.
  End N.

  (* Test with a functor *)
  Module F (X:S).
    Definition h := g + X.b.
    Recursive Extraction h.
    Extraction h.
  End F.

  (* Test elsewhere *)
  Recursive Extraction nat.
  Extraction nat.

  Module Type T.
    Definition foo := 0.
    Extraction foo.
  End T.

End M.
