Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : lsl 3 61 = -2305843009213693952).
Check (eq_refl (-2305843009213693952) <: lsl 3 61 = -2305843009213693952).
Check (eq_refl (-2305843009213693952) <<: lsl 3 61 = -2305843009213693952).
Definition compute1 := Eval compute in lsl 3 61.
Check (eq_refl compute1 : -2305843009213693952 = -2305843009213693952).

Check (eq_refl : lsl 2 62 = 0).
Check (eq_refl 0 <: lsl 2 62 = 0).
Check (eq_refl 0 <<: lsl 2 62 = 0).
Definition compute2 := Eval compute in lsl 2 62.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : lsl 4611686018427387903 63 = 0).
Check (eq_refl 0 <: lsl 4611686018427387903 63 = 0).
Check (eq_refl 0 <<: lsl 4611686018427387903 63 = 0).
Definition compute3 := Eval compute in lsl 4611686018427387903 63.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : lsl 4611686018427387903 62 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <:
  lsl 4611686018427387903 62 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <<:
  lsl 4611686018427387903 62 = -4611686018427387904).
Definition compute4 := Eval compute in lsl 4611686018427387903 62.
Check (eq_refl compute4 : -4611686018427387904 = -4611686018427387904).

Check (eq_refl : lsl 1 62 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <: lsl 1 62 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <<: lsl 1 62 = -4611686018427387904).
Definition compute5 := Eval compute in lsl 1 62.
Check (eq_refl compute5 : -4611686018427387904 = -4611686018427387904).

Check (eq_refl : lsl (-1)%sint63 1 = -2).
Check (eq_refl (-2) <: lsl (-1)%sint63 1 = -2).
Check (eq_refl (-2) <<: lsl (-1)%sint63 1 = -2).
Definition compute6 := Eval compute in lsl (-1)%sint63 1.
Check (eq_refl compute6 : -2 = -2).
