#[projections(primitive)]
Record test : Type := { f : nat }.
Section coercion.
  Coercion f : test >-> nat.
End coercion.
Section reduction.
  #[global] Opaque f.
End reduction.
Section hintopacity.
  #[global] Hint Opaque f : typeclass_instances.
End hintopacity.
