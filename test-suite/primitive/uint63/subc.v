Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : subc 3 2 = C0 1).
Check (eq_refl (C0 1) <: subc 3 2 = C0 1).
Check (eq_refl (C0 1) <<: subc 3 2 = C0 1).
Definition compute1 := Eval compute in subc 3 2.
Check (eq_refl compute1 : C0 1 = C0 1).

Check (eq_refl : subc 0 1 = C1 9223372036854775807).
Check (eq_refl (C1 9223372036854775807) <: subc 0 1 = C1 9223372036854775807).
Check (eq_refl (C1 9223372036854775807) <<: subc 0 1 = C1 9223372036854775807).
Definition compute2 := Eval compute in subc 0 1.
Check (eq_refl compute2 : C1 9223372036854775807 = C1 9223372036854775807).
