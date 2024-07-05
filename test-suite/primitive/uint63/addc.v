Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : addc 2 3 = C0 5).
Check (eq_refl (C0 5) <: addc 2 3 = C0 5).
Check (eq_refl (C0 5) <<: addc 2 3 = C0 5).
Definition compute1 := Eval compute in addc 2 3.
Check (eq_refl compute1 : C0 5 = C0 5).

Check (eq_refl : addc 9223372036854775807 2 = C1 1).
Check (eq_refl (C1 1) <: addc 9223372036854775807 2 = C1 1).
Check (eq_refl (C1 1) <<: addc 9223372036854775807 2 = C1 1).
Definition compute2 := Eval compute in addc 9223372036854775807 2.
Check (eq_refl compute2 : C1 1 = C1 1).
