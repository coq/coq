Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

Check (eq_refl : 2 + 3 = 5).
Check (eq_refl 5 <: 2 + 3 = 5).
Check (eq_refl 5 <<: 2 + 3 = 5).
Definition compute1 := Eval compute in 2 + 3.
Check (eq_refl compute1 : 5 = 5).

Check (eq_refl : 4611686018427387903 + 1 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <:
  4611686018427387903 + 1 = -4611686018427387904).
Check (eq_refl (-4611686018427387904) <<:
  4611686018427387903 + 1 = -4611686018427387904).
Definition compute2 := Eval compute in 4611686018427387903 + 1.
Check (eq_refl compute2 : -4611686018427387904 = -4611686018427387904).

Check (eq_refl : 2 - 3 = -1).
Check (eq_refl (-1) <: 2 - 3 = -1).
Check (eq_refl (-1) <<: 2 - 3 = -1).
Definition compute3 := Eval compute in 2 - 3.
Check (eq_refl compute3 : -1 = -1).
