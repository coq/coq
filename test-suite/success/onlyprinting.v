Notation "x ++ y" := (plus x y) (only printing).

Fail Check 0 ++ 0.

Notation "x + y" := (max x y) (only printing).

Check (eq_refl : 42 + 18 = 60).
