Class C := {}.

Definition useC {c:C} := nat.

Inductive foo {a b : C} := CC : useC -> foo.
(* If TC search runs before parameter unification it will pick the
   wrong instance for the first parameter.

   useC makes sure we don't completely skip TC search.
*)
