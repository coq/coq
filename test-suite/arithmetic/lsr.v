Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 6917529027641081856 >> 61 = 3).
Check (eq_refl 3 <: 6917529027641081856 >> 61 = 3).
Check (eq_refl 3 <<: 6917529027641081856 >> 61 = 3).
Definition compute1 := Eval compute in 6917529027641081856 >> 61.
Check (eq_refl compute1 : 3 = 3).

Check (eq_refl : 2305843009213693952 >> 62 = 0).
Check (eq_refl 0 <: 2305843009213693952 >> 62 = 0).
Check (eq_refl 0 <<: 2305843009213693952 >> 62 = 0).
Definition compute2 := Eval compute in 2305843009213693952 >> 62.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : 9223372036854775807 >> 64 = 0).
Check (eq_refl 0 <: 9223372036854775807 >> 64 = 0).
Check (eq_refl 0 <<: 9223372036854775807 >> 64 = 0).
Definition compute3 := Eval compute in 9223372036854775807 >> 64.
Check (eq_refl compute3 : 0 = 0).
