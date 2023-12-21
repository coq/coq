Require TestSuite.list.
Import list.ListNotations.

Parameter Foo : nat -> nat.

Delimit Scope Foo_scope with F.

Notation " [ x ] " := (Foo x) : Foo_scope.

Check ([1] : nat)%F.
