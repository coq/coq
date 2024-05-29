(* Check that untypable beta-expansion are trapped *)

Parameter A : nat -> Type.
Parameter n : nat.
Parameter P : forall m : nat, m = n -> Prop.

Goal forall p : n = n, P n p.
intro.
Fail pattern n, p.
Abort.
