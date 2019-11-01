Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : subcarryc 3 1 = C0 1).
Check (eq_refl (C0 1) <: subcarryc 3 1 = C0 1).
Check (eq_refl (C0 1) <<: subcarryc 3 1 = C0 1).
Definition compute1 := Eval compute in subcarryc 3 1.
Check (eq_refl compute1 : C0 1 = C0 1).

Check (eq_refl : subcarryc 0 1 = C1 9223372036854775806).
Check (eq_refl (C1 9223372036854775806) <: subcarryc 0 1 = C1 9223372036854775806).
Check (eq_refl (C1 9223372036854775806) <<: subcarryc 0 1 = C1 9223372036854775806).
Definition compute2 := Eval compute in subcarryc 0 1.
Check (eq_refl compute2 : C1 9223372036854775806 = C1 9223372036854775806).
