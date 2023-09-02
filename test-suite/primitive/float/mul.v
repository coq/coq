Require Import ZArith Uint63 Floats.

Open Scope float_scope.

Definition huge := Eval compute in Z.ldexp one 1023%Z.
Definition tiny := Eval compute in Z.ldexp one (-1023)%Z.

Check (eq_refl : huge * tiny = one).

Check (eq_refl : huge * huge = infinity).

Check (eq_refl : one * nan = nan).

Check (eq_refl : infinity * infinity = infinity).

Check (eq_refl : infinity * neg_infinity = neg_infinity).

Check (eq_refl : zero * zero = zero).
Check (eq_refl : neg_zero * zero = neg_zero).
Check (eq_refl : neg_zero * neg_zero = zero).
Check (eq_refl : zero * neg_zero = neg_zero).

Check (eq_refl : huge * neg_infinity = neg_infinity).

Check (eq_refl : one * tiny = tiny).
Check (eq_refl : one * huge = huge).
Check (eq_refl : zero * huge = zero).
Check (eq_refl : zero * (-huge) = neg_zero).

Check (eq_refl : zero * infinity = nan).
Check (eq_refl : neg_infinity * zero = nan).
