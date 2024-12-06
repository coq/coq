Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : sub 3 2 = 1).
Check (eq_refl 1 <: sub 3 2 = 1).
Check (eq_refl 1 <<: sub 3 2 = 1).
Definition compute1 := Eval compute in sub 3 2.
Check (eq_refl compute1 : 1 = 1).

Check (eq_refl : sub 0 1 = -1).
Check (eq_refl (-1) <: sub 0 1 = -1).
Check (eq_refl (-1) <<: sub 0 1 = -1).
Definition compute2 := Eval compute in sub 0 1.
Check (eq_refl compute2 : -1 = -1).

Check (eq_refl : sub (-4611686018427387904)%sint63 1 = 4611686018427387903).
Check (eq_refl 4611686018427387903 <:
  sub (-4611686018427387904)%sint63 1 = 4611686018427387903).
Check (eq_refl 4611686018427387903 <<:
  sub (-4611686018427387904)%sint63 1 = 4611686018427387903).
Definition compute3 := Eval compute in sub (-4611686018427387904)%sint63 1.
Check (eq_refl compute3 : 4611686018427387903 = 4611686018427387903).
