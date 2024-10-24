Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : mul 2 3 = 6).
Check (eq_refl 6 <: mul 2 3 = 6).
Check (eq_refl 6 <<: mul 2 3 = 6).
Definition compute1 := Eval compute in mul 2 3.
Check (eq_refl compute1 : 6 = 6).

Check (eq_refl : mul 9223372036854775807 2 = 9223372036854775806).
Check (eq_refl 9223372036854775806 <: mul 9223372036854775807 2 = 9223372036854775806).
Check (eq_refl 9223372036854775806 <<: mul 9223372036854775807 2 = 9223372036854775806).
Definition compute2 := Eval compute in mul 9223372036854775807 2.
Check (eq_refl compute2 : 9223372036854775806 = 9223372036854775806).
