(* Forbid unchecked fix on a non-inductive main argument *)

Unset Guard Checking.

Fail Fixpoint bad (x:unit -> nat) {struct x} : nat := x tt.
