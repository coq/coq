Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : add 2 3 = 5).
Check (eq_refl 5 <: add 2 3 = 5).
Check (eq_refl 5 <<: add 2 3 = 5).

Definition compute1 := Eval compute in add 2 3.
Check (eq_refl compute1 : 5 = 5).

Check (eq_refl : add 9223372036854775807 1 = 0).
Check (eq_refl 0 <: add 9223372036854775807 1 = 0).
Check (eq_refl 0 <<: add 9223372036854775807 1 = 0).
Definition compute2 := Eval compute in add 9223372036854775807 1.
Check (eq_refl compute2 : 0 = 0).
