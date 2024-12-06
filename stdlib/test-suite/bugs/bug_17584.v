From Stdlib Require Import RIneq.

Goal forall x y, (/(x * y) = 0)%R -> True.
Proof. intros x y H.
field_simplify in H.
Abort.
