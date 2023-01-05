Inductive boolε : bool -> Type :=
| trueε : boolε true
| falseε : boolε false.

(* Check branch sort inference with implicit Prop ⊆ Type cumulativity *)
Definition test (x : boolε true) :=
match x with
| trueε => I
| falseε => tt
end.
