Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : 1 =? 1 = true).
Check (eq_refl true <: 1 =? 1 = true).
Check (eq_refl true <<: 1 =? 1 = true).
Definition compute1 := Eval compute in 1 =? 1.
Check (eq_refl compute1 : true = true).

Check (eq_refl : 4611686018427387903 =? 0 = false).
Check (eq_refl false <: 4611686018427387903 =? 0 = false).
Check (eq_refl false <<: 4611686018427387903 =? 0 = false).
Definition compute2 := Eval compute in 4611686018427387903 =? 0.
Check (eq_refl compute2 : false = false).
