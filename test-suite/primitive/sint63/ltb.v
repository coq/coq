Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : ltsb 1 1 = false).
Check (eq_refl false <: ltsb 1 1 = false).
Check (eq_refl false <<: ltsb 1 1 = false).
Definition compute1 := Eval compute in ltsb 1 1.
Check (eq_refl compute1 : false = false).

Check (eq_refl : ltsb 1 2 = true).
Check (eq_refl true <: ltsb 1 2 = true).
Check (eq_refl true <<: ltsb 1 2 = true).
Definition compute2 := Eval compute in ltsb 1 2.
Check (eq_refl compute2 : true = true).

Check (eq_refl : ltsb 4611686018427387903 0 = false).
Check (eq_refl false <: ltsb 4611686018427387903 0 = false).
Check (eq_refl false <<: ltsb 4611686018427387903 0 = false).
Definition compute3 := Eval compute in ltsb 4611686018427387903 0.
Check (eq_refl compute3 : false = false).

Check (eq_refl : ltsb 1 (-1)%sint63 = false).
Check (eq_refl false <: ltsb 1 (-1)%sint63 = false).
Check (eq_refl false <<: ltsb 1 (-1)%sint63 = false).
Definition compute4 := Eval compute in ltsb 1 (-1)%sint63.
Check (eq_refl compute4 : false = false).
