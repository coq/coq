#[arity="1"]
Definition relation (A : Type) := A -> A -> Type.
About relation.
Check relation.

Definition test A := relation A.
