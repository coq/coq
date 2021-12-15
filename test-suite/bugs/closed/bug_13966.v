Inductive expr  := Const : nat -> expr.

Declare Custom Entry expr.
Notation "'[' e ']'" := e (e custom expr at level 0).
Notation "x" := (Const x) (in custom expr at level 0, x bigint).
Fail Notation "x" := x (in custom expr at level 0, x ident).
