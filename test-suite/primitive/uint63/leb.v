Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : leb 1 1 = true).
Check (eq_refl true <: leb 1 1 = true).
Check (eq_refl true <<: leb 1 1 = true).
Definition compute1 := Eval compute in leb 1 1.
Check (eq_refl compute1 : true = true).

Check (eq_refl : leb 1 2 = true).
Check (eq_refl true <: leb 1 2 = true).
Check (eq_refl true <<: leb 1 2 = true).
Definition compute2 := Eval compute in leb 1 2.
Check (eq_refl compute2 : true = true).

Check (eq_refl : leb 9223372036854775807 0 = false).
Check (eq_refl false <: leb 9223372036854775807 0 = false).
Check (eq_refl false <<: leb 9223372036854775807 0 = false).
Definition compute3 := Eval compute in leb 9223372036854775807 0.
Check (eq_refl compute3 : false = false).
