Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : mul 2 3 = 6).
Check (eq_refl 6 <: mul 2 3 = 6).
Check (eq_refl 6 <<: mul 2 3 = 6).
Definition compute1 := Eval compute in mul 2 3.
Check (eq_refl compute1 : 6 = 6).

Check (eq_refl : mul (-2)%sint63 3 = -6).
Check (eq_refl (-6) <: mul (-2)%sint63 3 = -6).
Check (eq_refl (-6) <<: mul (-2)%sint63 3 = -6).
Definition compute2 := Eval compute in mul (-2)%sint63 3.
Check (eq_refl compute2 : -6 = -6).

Check (eq_refl : mul 2 (-3)%sint63 = -6).
Check (eq_refl (-6) <: mul 2 (-3)%sint63 = -6).
Check (eq_refl (-6) <<: mul 2 (-3)%sint63 = -6).
Definition compute3 := Eval compute in mul 2 (-3)%sint63.
Check (eq_refl compute3 : -6 = -6).

Check (eq_refl : mul (-2)%sint63 (-3)%sint63 = 6).
Check (eq_refl 6 <: mul (-2)%sint63 (-3)%sint63 = 6).
Check (eq_refl 6 <<: mul (-2)%sint63 (-3)%sint63 = 6).
Definition compute4 := Eval compute in mul (-2)%sint63 (-3)%sint63.
Check (eq_refl compute4 : 6 = 6).

Check (eq_refl : mul 4611686018427387903 2 = -2).
Check (eq_refl (-2) <: mul 4611686018427387903 2 = -2).
Check (eq_refl (-2) <<: mul 4611686018427387903 2 = -2).
Definition compute5 := Eval compute in mul 4611686018427387903 2.
Check (eq_refl compute5 : -2 = -2).
