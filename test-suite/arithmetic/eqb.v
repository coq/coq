Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 1 == 1 = true).
Check (eq_refl true <: 1 == 1 = true).
Check (eq_refl true <<: 1 == 1 = true).
Definition compute1 := Eval compute in 1 == 1.
Check (eq_refl compute1 : true = true).

Check (eq_refl : 9223372036854775807 == 0 = false).
Check (eq_refl false <: 9223372036854775807 == 0 = false).
Check (eq_refl false <<: 9223372036854775807 == 0 = false).
Definition compute2 := Eval compute in 9223372036854775807 == 0.
Check (eq_refl compute2 : false = false).
