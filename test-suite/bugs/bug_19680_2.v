#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.
#[local] Set Decidable Equality Schemes.

Inductive option (A:Type) : Type :=
| Some : A -> option A
| None : option A.
