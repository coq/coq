Reserved Notation "x :-) y" (at level 50, only printing).

Notation "x :-) y" := (plus x y).

Check 0 + 0.

Fail Notation "x :-) y" := (x * y) (at level 45).
