Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : 6 mod 3 = 0).
Check (eq_refl 0 <: 6 mod 3 = 0).
Check (eq_refl 0 <<: 6 mod 3 = 0).
Definition compute1 := Eval compute in 6 mod 3.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : -6 mod 3 = 0).
Check (eq_refl 0 <: -6 mod 3 = 0).
Check (eq_refl 0 <<: -6 mod 3 = 0).
Definition compute2 := Eval compute in -6 mod 3.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : 6 mod -3 = 0).
Check (eq_refl 0 <: 6 mod -3 = 0).
Check (eq_refl 0 <<: 6 mod -3 = 0).
Definition compute3 := Eval compute in 6 mod -3.
Check (eq_refl compute3 : 0 = 0).

Check (eq_refl : -6 mod -3 = 0).
Check (eq_refl 0 <: -6 mod -3 = 0).
Check (eq_refl 0 <<: -6 mod -3 = 0).
Definition compute4 := Eval compute in -6 mod -3.
Check (eq_refl compute4 : 0 = 0).

Check (eq_refl : 5 mod 3 = 2).
Check (eq_refl 2 <: 5 mod 3 = 2).
Check (eq_refl 2 <<: 5 mod 3 = 2).
Definition compute5 := Eval compute in 5 mod 3.
Check (eq_refl compute5 : 2 = 2).

Check (eq_refl : -5 mod 3 = -2).
Check (eq_refl (-2) <: -5 mod 3 = -2).
Check (eq_refl (-2) <<: -5 mod 3 = -2).
Definition compute6 := Eval compute in -5 mod 3.
Check (eq_refl compute6 : -2 = -2).

Check (eq_refl : 5 mod -3 = 2).
Check (eq_refl 2 <: 5 mod -3 = 2).
Check (eq_refl 2 <<: 5 mod -3 = 2).
Definition compute7 := Eval compute in 5 mod -3.
Check (eq_refl compute7 : 2 = 2).

Check (eq_refl : -5 mod -3 = -2).
Check (eq_refl (-2) <: -5 mod -3 = -2).
Check (eq_refl (-2) <<: -5 mod -3 = -2).
Definition compute8 := Eval compute in -5 mod -3.
Check (eq_refl compute8 : -2 = -2).
