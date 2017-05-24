(* An example showing a bug in the detection of free variables *)
(* "x" is not free in the common type of "x" and "y" *)

Check forall (x z:unit) (x y : match z as x return x=x with tt => eq_refl end = eq_refl), x=x.

(* An example showing a bug in the detection of bound variables *)

Goal forall x, match x return x = x with 0 => eq_refl | _ => eq_refl end = eq_refl.
intro.
match goal with
|- (match x as y in nat return y = y with O => _ | S n => _ end) = _ => assert (forall y, y = 0) end.
intro.
Check x0. (* Check that "y" has been bound to "x0" while matching "match x as x0 return x0=x0 with ... end" *)
Abort.
