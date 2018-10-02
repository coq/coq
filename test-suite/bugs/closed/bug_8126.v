(* See also output test Notations4.v *)

Inductive foo := tt.
Bind Scope foo_scope with foo.
Delimit Scope foo_scope with foo.
Notation "'HI'" := tt : foo_scope.
Definition myfoo (x : nat) (y : nat) (z : foo) := y.
Notation myfoo0 := (@myfoo 0).
Notation myfoo01 := (@myfoo0 1).
Check myfoo 0 1 HI. (* prints [myfoo0 1 HI], but should print [myfoo01 HI]  *)
Check myfoo0 1 HI. (* prints [myfoo0 1 HI], but should print [myfoo01 HI]  *)
Check myfoo01 tt. (* prints [myfoo0 1 HI], but should print [myfoo01 HI]  *)
Check myfoo01 HI. (* was failing *)
