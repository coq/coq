Require Import PrimInt63 PrimFloat.

Open Scope float_scope.

Definition three := Eval compute in of_uint63 3%uint63.
Definition nine := Eval compute in of_uint63 9%uint63.

Check (eq_refl : sqrt nine = three).

Check (eq_refl : sqrt zero = zero).
Check (eq_refl : sqrt neg_zero = neg_zero).
Check (eq_refl : sqrt one = one).
Check (eq_refl : sqrt (-one) = nan).
Check (eq_refl : sqrt infinity = infinity).
Check (eq_refl : sqrt neg_infinity = nan).
