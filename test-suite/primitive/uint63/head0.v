Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : head0 3 = 61).
Check (eq_refl 61 <: head0 3 = 61).
Check (eq_refl 61 <<: head0 3 = 61).
Definition compute1 := Eval compute in head0 3.
Check (eq_refl compute1 : 61 = 61).

Check (eq_refl : head0 4611686018427387904 = 0).
Check (eq_refl 0 <: head0 4611686018427387904 = 0).
Check (eq_refl 0 <<: head0 4611686018427387904 = 0).
Definition compute2 := Eval compute in head0 4611686018427387904.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : head0 0 = 63).
Check (eq_refl 63 <: head0 0 = 63).
Check (eq_refl 63 <<: head0 0 = 63).
Definition compute3 := Eval compute in head0 0.
Check (eq_refl compute3 : 63 = 63).
