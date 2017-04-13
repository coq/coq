(* An example showing a bug in the detection of free variables *)
(* "x" is not free in the common type of "x" and "y" *)

Check forall (x z:unit) (x y : match z as x return x=x with tt => eq_refl end = eq_refl), x=x.

