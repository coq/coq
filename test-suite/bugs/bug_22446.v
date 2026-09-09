Module Type T. Parameter Inline t : Type. Parameter u : t -> t. End T.
Module A. Definition t := nat. Definition u (x : nat) := x. End A.

Module F (X : T) := X.
Module H (X : T). Include F X. End H.
Module R := H A.

Notation "1" := true.
Check R.u 1.
