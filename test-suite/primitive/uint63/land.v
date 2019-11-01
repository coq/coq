Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 0 land 0 = 0).
Check (eq_refl 0 <: 0 land 0 = 0).
Check (eq_refl 0 <<: 0 land 0 = 0).
Definition compute1 := Eval compute in 0 land 0.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : 9223372036854775807 land 0 = 0).
Check (eq_refl 0 <: 9223372036854775807 land 0 = 0).
Check (eq_refl 0 <<: 9223372036854775807 land 0 = 0).
Definition compute2 := Eval compute in 9223372036854775807 land 0.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : 0 land 9223372036854775807 = 0).
Check (eq_refl 0 <: 0 land 9223372036854775807 = 0).
Check (eq_refl 0 <<: 0 land 9223372036854775807 = 0).
Definition compute3 := Eval compute in 0 land 9223372036854775807.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : 9223372036854775807 land 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: 9223372036854775807 land 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: 9223372036854775807 land 9223372036854775807 = 9223372036854775807).
Definition compute4 := Eval compute in 9223372036854775807 land 9223372036854775807.
Check (eq_refl compute4 : 9223372036854775807 = 9223372036854775807).
