Require Import ZArith Int63 Floats.

Open Scope float_scope.

Definition two := Eval compute in of_int63 2%int63.
Definition three := Eval compute in of_int63 3%int63.
Definition five := Eval compute in of_int63 5%int63.

Check (eq_refl : two + three = five).
(*Check (eq_refl five <: two + three = five).
Check (eq_refl 5 <<: two + three = five).*)
Definition compute1 := Eval compute in two + three.
Check (eq_refl compute1 : five = five).

Definition huge := Eval compute in ldexp one 1023%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.

Check (eq_refl : huge + tiny = huge).
(*Check (eq_refl huge <: huge + tiny = huge).
Check (eq_refl huge <<: huge + tiny = huge).*)
Definition compute2 := Eval compute in huge + tiny.
Check (eq_refl compute2 : huge = huge).

Check (eq_refl : huge + huge = infinity).
Definition compute3 := Eval compute in huge + huge.
Check (eq_refl compute3 : infinity = infinity).

Check (eq_refl : one + nan = nan).
Definition compute4 := Eval compute in one + nan.
Check (eq_refl compute4 : nan = nan).

Check (eq_refl : infinity + infinity = infinity).
Definition compute5 := Eval compute in infinity + infinity.
Check (eq_refl compute5 : infinity = infinity).

Check (eq_refl : infinity + neg_infinity = nan).
Definition compute6 := Eval compute in infinity + neg_infinity.
Check (eq_refl compute6 : nan = nan).

Check (eq_refl : zero + zero = zero).
Check (eq_refl : neg_zero + zero = zero).
Check (eq_refl : neg_zero + neg_zero = neg_zero).
Check (eq_refl : zero + neg_zero = zero).

Check (eq_refl : huge + neg_infinity = neg_infinity).
