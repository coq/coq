Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : 2 * 3 = 6).
Check (eq_refl 6 <: 2 * 3 = 6).
Check (eq_refl 6 <<: 2 * 3 = 6).
Definition compute1 := Eval compute in 2 * 3.
Check (eq_refl compute1 : 6 = 6).

Check (eq_refl : -2 * 3 = -6).
Check (eq_refl (-6) <: -2 * 3 = -6).
Check (eq_refl (-6) <<: -2 * 3 = -6).
Definition compute2 := Eval compute in -2 * 3.
Check (eq_refl compute2 : -6 = -6).

Check (eq_refl : 2 * -3 = -6).
Check (eq_refl (-6) <: 2 * -3 = -6).
Check (eq_refl (-6) <<: 2 * -3 = -6).
Definition compute3 := Eval compute in 2 * -3.
Check (eq_refl compute3 : -6 = -6).

Check (eq_refl : -2 * -3 = 6).
Check (eq_refl 6 <: -2 * -3 = 6).
Check (eq_refl 6 <<: -2 * -3 = 6).
Definition compute4 := Eval compute in -2 * -3.
Check (eq_refl compute4 : 6 = 6).

Check (eq_refl : 4611686018427387903 * 2 = -2).
Check (eq_refl (-2) <: 4611686018427387903 * 2 = -2).
Check (eq_refl (-2) <<: 4611686018427387903 * 2 = -2).
Definition compute5 := Eval compute in 4611686018427387903 * 2.
Check (eq_refl compute5 : -2 = -2).
