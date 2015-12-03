Module foo.
  Notation x := ltac:(exact I).
End foo.
Module bar.
  Include foo.
End bar.
