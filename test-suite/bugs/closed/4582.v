Require List.
Import List.ListNotations.

Variable Foo : nat -> nat.

Delimit Scope Foo_scope with F.

Notation " [ x ] " := (Foo x) : Foo_scope.

Check ([1] : nat)%F.
