Require Import TestSuite.sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : asr (-2305843009213693952)%sint63 61 = -1).
Check (eq_refl (-1) <: asr (-2305843009213693952)%sint63 61 = -1).
Check (eq_refl (-1) <<: asr (-2305843009213693952)%sint63 61 = -1).
Definition compute1 := Eval compute in asr (-2305843009213693952)%sint63 61.
Check (eq_refl compute1 : -1 = -1).

Check (eq_refl : asr 2305843009213693952 62 = 0).
Check (eq_refl 0 <: asr 2305843009213693952 62 = 0).
Check (eq_refl 0 <<: asr 2305843009213693952 62 = 0).
Definition compute2 := Eval compute in asr 2305843009213693952 62.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : asr 4611686018427387903 63 = 0).
Check (eq_refl 0 <: asr 4611686018427387903 63 = 0).
Check (eq_refl 0 <<: asr 4611686018427387903 63 = 0).
Definition compute3 := Eval compute in asr 4611686018427387903 63.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : asr (-1)%sint63 1 = -1).
Check (eq_refl (-1) <: asr (-1)%sint63 1 = -1).
Check (eq_refl (-1) <<: asr (-1)%sint63 1 = -1).
Definition compute4 := Eval compute in asr (-1)%sint63 1.
Check (eq_refl compute4 : -1 = -1).

Check (eq_refl : asr (-1)%sint63 (-1)%sint63 = 0).
Check (eq_refl 0 <: asr (-1)%sint63 (-1)%sint63 = 0).
Check (eq_refl 0 <<: asr (-1)%sint63 (-1)%sint63 = 0).
Definition compute5 := Eval compute in asr (-1)%sint63 (-1)%sint63.
Check (eq_refl compute5 : 0 = 0).

Check (eq_refl : asr 73 (-2)%sint63 = 0).
Check (eq_refl 0 <: asr 73 (-2)%sint63 = 0).
Check (eq_refl 0 <<: asr 73 (-2)%sint63 = 0).
Definition compute6 := Eval compute in asr 73 (-2)%sint63.
Check (eq_refl compute6 : 0 = 0).
