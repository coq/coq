(* Check that untypable beta-expansion are trapped *)

Variable A : nat -> Type.
Variable n : nat.
Variable P : forall m : nat, m = n -> Prop.

Goal forall p : n = n, P n p.
intro.
Fail pattern n, p.
