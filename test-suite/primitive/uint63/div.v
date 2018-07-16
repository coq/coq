Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 6 / 3 = 2).
Check (eq_refl 2 <: 6 / 3 = 2).
Check (eq_refl 2 <<: 6 / 3 = 2).
Definition compute1 := Eval compute in 6 / 3.
Check (eq_refl compute1 : 2 = 2).

Check (eq_refl : 3 / 2 = 1).
Check (eq_refl 1 <: 3 / 2 = 1).
Check (eq_refl 1 <<: 3 / 2 = 1).
Definition compute2 := Eval compute in 3 / 2.
Check (eq_refl compute2 : 1 = 1).
