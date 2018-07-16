Require Import ZArith Int63 Floats.

Open Scope float_scope.

Definition two := Eval compute in of_int63 2%int63.
Definition three := Eval compute in of_int63 3%int63.
Definition six := Eval compute in of_int63 6%int63.

Check (eq_refl : six / three = two).
Definition compute1 := Eval compute in six / three.
Check (eq_refl compute1 : two = two).

Definition huge := Eval compute in ldexp one 1023%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.

Check (eq_refl : huge / tiny = infinity).
Definition compute2 := Eval compute in huge / tiny.
Check (eq_refl compute2 : infinity = infinity).

Check (eq_refl : huge / huge = one).
Definition compute3 := Eval compute in huge / huge.
Check (eq_refl compute3 : one = one).

Check (eq_refl : one / nan = nan).
Definition compute4 := Eval compute in one / nan.
Check (eq_refl compute4 : nan = nan).

Check (eq_refl : infinity / infinity = nan).
Definition compute5 := Eval compute in infinity / infinity.
Check (eq_refl compute5 : nan = nan).

Check (eq_refl : infinity / neg_infinity = nan).
Definition compute6 := Eval compute in infinity / neg_infinity.
Check (eq_refl compute6 : nan = nan).

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
