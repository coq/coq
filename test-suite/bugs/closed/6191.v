(* Check a 8.7.1 regression in ring_simplify *)

Require Import ArithRing BinNat.
Goal forall f x, (2+x+f (N.to_nat 2)+3=4).
intros.
ring_simplify (2+x+f (N.to_nat 2)+3).
match goal with |- x + f (N.to_nat 2) + 5 = 4 => idtac end.
Abort.

Require Import ZArithRing BinInt.
Open Scope Z_scope.
Goal forall x, (2+x+3=4).
intros.
ring_simplify (2+x+3).
match goal with |- x+5 = 4 => idtac end.
Abort.
