Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 0 lxor 0 = 0).
Check (eq_refl 0 <: 0 lxor 0 = 0).
Check (eq_refl 0 <<: 0 lxor 0 = 0).
Definition compute1 := Eval compute in 0 lxor 0.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : 9223372036854775807 lxor 0 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: 9223372036854775807 lxor 0 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: 9223372036854775807 lxor 0 = 9223372036854775807).
Definition compute2 := Eval compute in 9223372036854775807 lxor 0.
Check (eq_refl compute2 : 9223372036854775807 = 9223372036854775807).

Check (eq_refl : 0 lxor 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: 0 lxor 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: 0 lxor 9223372036854775807 = 9223372036854775807).
Definition compute3 := Eval compute in 0 lxor 9223372036854775807.
Check (eq_refl compute3 : 9223372036854775807 = 9223372036854775807).

Check (eq_refl : 9223372036854775807 lxor 9223372036854775807 = 0).
Check (eq_refl 0 <: 9223372036854775807 lxor 9223372036854775807 = 0).
Check (eq_refl 0 <<: 9223372036854775807 lxor 9223372036854775807 = 0).
Definition compute4 := Eval compute in 9223372036854775807 lxor 9223372036854775807.
Check (eq_refl compute4 : 0 = 0).
