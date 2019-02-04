Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : tail0 2305843009213693952 = 61).
Check (eq_refl 61 <: tail0 2305843009213693952 = 61).
Check (eq_refl 61 <<: tail0 2305843009213693952 = 61).
Definition compute1 := Eval compute in tail0 2305843009213693952.
Check (eq_refl compute1 : 61 = 61).

Check (eq_refl : tail0 1 = 0).
Check (eq_refl 0 <: tail0 1 = 0).
Check (eq_refl 0 <<: tail0 1 = 0).
Definition compute2 := Eval compute in tail0 1.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : tail0 0 = 63).
Check (eq_refl 63 <: tail0 0 = 63).
Check (eq_refl 63 <<: tail0 0 = 63).
Definition compute3 := Eval compute in tail0 0.
Check (eq_refl compute3 : 63 = 63).
