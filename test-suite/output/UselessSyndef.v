Module M.
  Definition a := 0.
End M.
Module N.
  Notation a := M.a (only parsing).
End N.

Import M. Import N.

Check a.
