Require Import PrimFloat.

Open Scope float_scope.

Definition two := Eval compute in one + one.
Definition half := Eval compute in one / two.

Check (eq_refl : 1.5 = one + half).
Check (eq_refl : 15e-1 = one + half).
Check (eq_refl : 150e-2 = one + half).
Check (eq_refl : 0.15e+1 = one + half).
Check (eq_refl : 0.15e1 = one + half).
Check (eq_refl : 0.0015e3 = one + half).
