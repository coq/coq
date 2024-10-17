#[projections(primitive)]
Record test : Type := { f : nat }.
Section foo.
  #[global] Opaque f.
  Set Debug "backtrace".
End foo.
Section foo.
  #[global] Hint Opaque f : typeclass_instances.
  Set Debug "backtrace".
End foo.
