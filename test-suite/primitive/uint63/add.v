Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 2 + 3 = 5).
Check (eq_refl 5 <: 2 + 3 = 5).
Check (eq_refl 5 <<: 2 + 3 = 5).

Definition compute1 := Eval compute in 2 + 3.
Check (eq_refl compute1 : 5 = 5).

Check (eq_refl : 9223372036854775807 + 1 = 0).
Check (eq_refl 0 <: 9223372036854775807 + 1 = 0).
Check (eq_refl 0 <<: 9223372036854775807 + 1 = 0).
Definition compute2 := Eval compute in 9223372036854775807 + 1.
Check (eq_refl compute2 : 0 = 0).
