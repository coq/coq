Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 3 -c 2 = C0 1).
Check (eq_refl (C0 1) <: 3 -c 2 = C0 1).
Check (eq_refl (C0 1) <<: 3 -c 2 = C0 1).
Definition compute1 := Eval compute in 3 -c 2.
Check (eq_refl compute1 : C0 1 = C0 1).

Check (eq_refl : 0 -c 1 = C1 9223372036854775807).
Check (eq_refl (C1 9223372036854775807) <: 0 -c 1 = C1 9223372036854775807).
Check (eq_refl (C1 9223372036854775807) <<: 0 -c 1 = C1 9223372036854775807).
Definition compute2 := Eval compute in 0 -c 1.
Check (eq_refl compute2 : C1 9223372036854775807 = C1 9223372036854775807).
