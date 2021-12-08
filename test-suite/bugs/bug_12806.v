Require Import Ltac2.Ltac2.

Declare Scope my_scope.
Delimit Scope my_scope with my_scope.

Notation "###" := tt : my_scope.

Ltac2 Notation "bar" c(open_constr(my_scope)) := c.
Ltac2 Eval bar ###.
