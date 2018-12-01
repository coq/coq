(* Check notations scopes for terms % and %_ *)

Declare Scope A_scope.
Declare Scope B_scope.
Delimit Scope B_scope with B.

Variant t := T.
Definition f1 (x y : t) := x.
Definition f2 (x y : t) := y.

Notation "x * y" := (f1 x y) : A_scope.
Notation "x * y" := (f2 x y) : B_scope.

Set Printing All.

Local Open Scope A_scope.

Check T * T * T.
Check (T * T * T)%B.
Check (T * T * T)%_B.
