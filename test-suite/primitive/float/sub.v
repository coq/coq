Require Import ZArith Int63 Floats.

Open Scope float_scope.

Definition two := Eval compute in of_int63 2%int63.
Definition three := Eval compute in of_int63 3%int63.

Check (eq_refl : three - two = one).
Check (eq_refl one <: three - two = one).
Check (eq_refl one <<: three - two = one).
Definition compute1 := Eval compute in three - two.
Check (eq_refl compute1 : one = one).

Definition huge := Eval compute in ldexp one 1023%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.

Check (eq_refl : huge - tiny = huge).
Check (eq_refl huge <: huge - tiny = huge).
Check (eq_refl huge <<: huge - tiny = huge).
Definition compute2 := Eval compute in huge - tiny.
Check (eq_refl compute2 : huge = huge).

Check (eq_refl : huge - huge = zero).
Check (eq_refl zero <: huge - huge = zero).
Check (eq_refl zero <<: huge - huge = zero).
Definition compute3 := Eval compute in huge - huge.
Check (eq_refl compute3 : zero = zero).

Check (eq_refl : one - nan = nan).
Check (eq_refl nan <: one - nan = nan).
Check (eq_refl nan <<: one - nan = nan).
Definition compute4 := Eval compute in one - nan.
Check (eq_refl compute4 : nan = nan).

Check (eq_refl : infinity - infinity = nan).
Check (eq_refl nan <: infinity - infinity = nan).
Check (eq_refl nan <<: infinity - infinity = nan).
Definition compute5 := Eval compute in infinity - infinity.
Check (eq_refl compute5 : nan = nan).

Check (eq_refl : infinity - neg_infinity = infinity).
Check (eq_refl infinity <: infinity - neg_infinity = infinity).
Check (eq_refl infinity <<: infinity - neg_infinity = infinity).
Definition compute6 := Eval compute in infinity - neg_infinity.
Check (eq_refl compute6 : infinity = infinity).

Check (eq_refl : zero - zero = zero).
Check (eq_refl zero <: zero - zero = zero).
Check (eq_refl zero <<: zero - zero = zero).
Check (eq_refl : neg_zero - zero = neg_zero).
Check (eq_refl neg_zero <: neg_zero - zero = neg_zero).
Check (eq_refl neg_zero <<: neg_zero - zero = neg_zero).
Check (eq_refl : neg_zero - neg_zero = zero).
Check (eq_refl zero <: neg_zero - neg_zero = zero).
Check (eq_refl zero <<: neg_zero - neg_zero = zero).
Check (eq_refl : zero - neg_zero = zero).
Check (eq_refl zero <: zero - neg_zero = zero).
Check (eq_refl zero <<: zero - neg_zero = zero).

Check (eq_refl : huge - neg_infinity = infinity).
Check (eq_refl infinity <: huge - neg_infinity = infinity).
Check (eq_refl infinity <<: huge - neg_infinity = infinity).
