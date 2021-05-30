Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : (-2305843009213693952) >> 61 = -1).
Check (eq_refl (-1) <: (-2305843009213693952) >> 61 = -1).
Check (eq_refl (-1) <<: (-2305843009213693952) >> 61 = -1).
Definition compute1 := Eval compute in (-2305843009213693952) >> 61.
Check (eq_refl compute1 : -1 = -1).

Check (eq_refl : 2305843009213693952 >> 62 = 0).
Check (eq_refl 0 <: 2305843009213693952 >> 62 = 0).
Check (eq_refl 0 <<: 2305843009213693952 >> 62 = 0).
Definition compute2 := Eval compute in 2305843009213693952 >> 62.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : 4611686018427387903 >> 63 = 0).
Check (eq_refl 0 <: 4611686018427387903 >> 63 = 0).
Check (eq_refl 0 <<: 4611686018427387903 >> 63 = 0).
Definition compute3 := Eval compute in 4611686018427387903 >> 63.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : (-1) >> 1 = -1).
Check (eq_refl (-1) <: (-1) >> 1 = -1).
Check (eq_refl (-1) <<: (-1) >> 1 = -1).
Definition compute4 := Eval compute in (-1) >> 1.
Check (eq_refl compute4 : -1 = -1).

Check (eq_refl : (-1) >> (-1) = 0).
Check (eq_refl 0 <: (-1) >> (-1) = 0).
Check (eq_refl 0 <<: (-1) >> (-1) = 0).
Definition compute5 := Eval compute in (-1) >> (-1).
Check (eq_refl compute5 : 0 = 0).

Check (eq_refl : 73 >> (-2) = 0).
Check (eq_refl 0 <: 73 >> (-2) = 0).
Check (eq_refl 0 <<: 73 >> (-2) = 0).
Definition compute6 := Eval compute in 73 >> (-2).
Check (eq_refl compute6 : 0 = 0).
