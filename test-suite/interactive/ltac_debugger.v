Set Ltac Debug.

Ltac my_tac :=
  let i := 1 in
  let con := constr:(forall a b c : nat,
    (a + b) * c = a * c + b * c) in
  idtac "A"; idtac "B"; idtac "C".

Goal True.
my_tac.
