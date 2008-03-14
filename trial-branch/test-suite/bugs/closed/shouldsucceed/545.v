Require Export Reals.

Parameter toto : nat -> nat -> nat.

Notation " e # f " := (toto e f) (at level 30, f at level 0).
