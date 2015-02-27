Module foo.
  Notation x := $(exact I)$.
End foo.
Module bar.
  Include foo.
End bar.
