Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : eqb 1 1 = true).
Check (eq_refl true <: eqb 1 1 = true).
Check (eq_refl true <<: eqb 1 1 = true).
Definition compute1 := Eval compute in eqb 1 1.
Check (eq_refl compute1 : true = true).

Check (eq_refl : eqb 9223372036854775807 0 = false).
Check (eq_refl false <: eqb 9223372036854775807 0 = false).
Check (eq_refl false <<: eqb 9223372036854775807 0 = false).
Definition compute2 := Eval compute in eqb 9223372036854775807 0.
Check (eq_refl compute2 : false = false).
