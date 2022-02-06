(* Test transitive dependencies for clearbody *)
Goal let U := Set in forall T : U, T -> True.
intros.
Fail clearbody U.
Abort.
