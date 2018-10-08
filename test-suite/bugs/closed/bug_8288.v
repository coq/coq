Set Universe Polymorphism.
Set Printing Universes.

Set Polymorphic Inductive Cumulativity.

Inductive foo := C : (forall A : Type -> Type, A Type) -> foo.
(* anomaly invalid subtyping relation *)
