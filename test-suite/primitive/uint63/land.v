Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : land 0 0 = 0).
Check (eq_refl 0 <: land 0 0 = 0).
Check (eq_refl 0 <<: land 0 0 = 0).
Definition compute1 := Eval compute in land 0 0.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : land 9223372036854775807 0 = 0).
Check (eq_refl 0 <: land 9223372036854775807 0 = 0).
Check (eq_refl 0 <<: land 9223372036854775807 0 = 0).
Definition compute2 := Eval compute in land 9223372036854775807 0.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : land 0 9223372036854775807 = 0).
Check (eq_refl 0 <: land 0 9223372036854775807 = 0).
Check (eq_refl 0 <<: land 0 9223372036854775807 = 0).
Definition compute3 := Eval compute in land 0 9223372036854775807.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : land 9223372036854775807 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: land 9223372036854775807 9223372036854775807 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: land 9223372036854775807 9223372036854775807 = 9223372036854775807).
Definition compute4 := Eval compute in land 9223372036854775807 9223372036854775807.
Check (eq_refl compute4 : 9223372036854775807 = 9223372036854775807).
