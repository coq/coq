Set Universe Polymorphism.
Notation Type1 := ltac:(let U := constr:(Type) in let gt := constr:(Set : U) in exact U) (only parsing).
Inductive Empty : Type1 := .
Fail Check Empty : Set.
(* Toplevel input, characters 15-116:
Error: Conversion test raised an anomaly *)
(* Now we make sure it's not an anomaly *)
Goal True.
Proof.
  try exact (let x := Empty : Set in I).
  exact I.
Defined.
