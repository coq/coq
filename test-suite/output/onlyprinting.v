Module A.

Reserved Notation "x :-) y" (at level 50, only printing).

Notation "x :-) y" := (plus x y).

Check 0 + 0.

End A.

Module B.

Notation "x +_a y" := (plus x y) (at level 50) : nat_scope.
Check 1 +_a 2.
Notation "x +_b y" := (plus x y) (at level 50) : nat_scope.
Check 1 +_a 2.
Check 1 +_b 2.
Notation "x +_c y" := (plus x y) (at level 50, only printing) : nat_scope.
Check 1 +_a 2.
Check 1 +_b 2.
Print Scope nat_scope.
Deactivate Notation "_ +_c _" : nat_scope.
Check 1 +_a 2.
Deactivate Notation "x +_b y" : nat_scope.
Check 1 +_a 2.
Deactivate Notation "_ +_a _" (only printing) : nat_scope.
Check 1 +_a 2.
Activate Notation "a +_c b" (only printing) : nat_scope.
Check 1 +_a 2.

End B.
