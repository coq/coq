Set Universe Polymorphism.
Inductive A@{} : Set := B : ltac:(let y := constr:(Type) in exact nat) -> A.
