Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 3 - 2 = 1).
Check (eq_refl 1 <: 3 - 2 = 1).
Check (eq_refl 1 <<: 3 - 2 = 1).
Definition compute1 := Eval compute in 3 - 2.
Check (eq_refl compute1 : 1 = 1).

Check (eq_refl : 0 - 1 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <: 0 - 1 = 9223372036854775807).
Check (eq_refl 9223372036854775807 <<: 0 - 1 = 9223372036854775807).
Definition compute2 := Eval compute in 0 - 1.
Check (eq_refl compute2 : 9223372036854775807 = 9223372036854775807).
