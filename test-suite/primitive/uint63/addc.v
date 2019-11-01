Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 2 +c 3 = C0 5).
Check (eq_refl (C0 5) <: 2 +c 3 = C0 5).
Check (eq_refl (C0 5) <<: 2 +c 3 = C0 5).
Definition compute1 := Eval compute in 2 +c 3.
Check (eq_refl compute1 : C0 5 = C0 5).

Check (eq_refl : 9223372036854775807 +c 2 = C1 1).
Check (eq_refl (C1 1) <: 9223372036854775807 +c 2 = C1 1).
Check (eq_refl (C1 1) <<: 9223372036854775807 +c 2 = C1 1).
Definition compute2 := Eval compute in 9223372036854775807 +c 2.
Check (eq_refl compute2 : C1 1 = C1 1).
