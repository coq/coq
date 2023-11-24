Require Import ZArith Uint63 Floats.

Open Scope float_scope.

Definition huge := Eval compute in Z.ldexp one 1023%Z.
Definition tiny := Eval compute in Z.ldexp one (-1023)%Z.

Check (eq_refl : huge / tiny = infinity).

Check (eq_refl : huge / huge = one).

Check (eq_refl : one / nan = nan).

Check (eq_refl : infinity / infinity = nan).

Check (eq_refl : infinity / neg_infinity = nan).

Check (eq_refl : zero / zero = nan).
Check (eq_refl : neg_zero / zero = nan).

Check (eq_refl : huge / neg_infinity = neg_zero).

Check (eq_refl : one / tiny = huge).
Check (eq_refl : one / huge = tiny).
Check (eq_refl : zero / huge = zero).
Check (eq_refl : zero / (-huge) = neg_zero).

Check (eq_refl : tiny / one = tiny).
Check (eq_refl : huge / one = huge).
Check (eq_refl : infinity / one = infinity).

Check (eq_refl : zero / infinity = zero).
Check (eq_refl : infinity / zero = infinity).
