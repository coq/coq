Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : addcarryc 2 3 = C0 6).
Check (eq_refl (C0 6) <: addcarryc 2 3 = C0 6).
Check (eq_refl (C0 6) <<: addcarryc 2 3 = C0 6).
Definition compute1 := Eval compute in addcarryc 2 3.
Check (eq_refl compute1 : C0 6 = C0 6).

Check (eq_refl : addcarryc 9223372036854775807 2 = C1 2).
Check (eq_refl (C1 2) <: addcarryc 9223372036854775807 2 = C1 2).
Check (eq_refl (C1 2) <<: addcarryc 9223372036854775807 2 = C1 2).
Definition compute2 := Eval compute in addcarryc 9223372036854775807 2.
Check (eq_refl compute2 : C1 2 = C1 2).
