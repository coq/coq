Require Import ZArith Uint63 Floats.

Open Scope float_scope.

Definition huge := Eval compute in Z.ldexp one 1023%Z.
Definition tiny := Eval compute in Z.ldexp one (-1023)%Z.

Check (eq_refl : huge - tiny = huge).

Check (eq_refl : huge - huge = zero).

Check (eq_refl : one - nan = nan).

Check (eq_refl : infinity - infinity = nan).

Check (eq_refl : infinity - neg_infinity = infinity).

Check (eq_refl : zero - zero = zero).
Check (eq_refl : neg_zero - zero = neg_zero).
Check (eq_refl : neg_zero - neg_zero = zero).
Check (eq_refl : zero - neg_zero = zero).

Check (eq_refl : huge - neg_infinity = infinity).
