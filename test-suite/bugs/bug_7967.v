Set Universe Polymorphism.
Inductive A@{} : Set := B : ltac:(let y := constr:(Type) in exact nat) -> A.

(* A similar bug *)
#[warning="context-outside-section"] Context (C := ltac:(let y := constr:(Type) in exact nat)).
Check C@{}.
