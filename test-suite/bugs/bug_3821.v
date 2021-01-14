Unset Strict Universe Declaration.
#[universes(template=no)]
Inductive quotient {A : Type@{i}} {B : Type@{j}} : Type@{max(i, j)} := .
