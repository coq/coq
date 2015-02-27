Module foo.
  Notation x := $(exact I)$.
End foo.
Module bar.
  Fail Include foo.
End bar.
