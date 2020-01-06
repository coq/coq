Section S.
  Variable (A:Type).
  #[universes(template)]
  Inductive bar (d:A) := .
End S.
Check bar nat 0.
