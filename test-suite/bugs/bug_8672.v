(* Was generating a dangling "pat" variable at some time *)

Notation "'plet' x := e 'in' t" :=
  ((fun H => let x := id H in t) e) (at level 0, x pattern).
Definition bla := plet (pair x y) := pair 1 2 in x.
