Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : sub 3 2 = 1).
Check (eq_refl 1 <: sub 3 2 = 1).
Check (eq_refl 1 <<: sub 3 2 = 1).
Definition compute1 := Eval compute in sub 3 2.
Check (eq_refl compute1 : 1 = 1).

Check (eq_refl : sub 0 1 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: sub 0 1 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: sub 0 1 = 9223372036854775807).
Definition compute2 := Eval compute in sub 0 1.
Check (eq_refl compute2 : 9223372036854775807 = 9223372036854775807).
