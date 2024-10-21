Require Import BinNums IntDef PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : mulc 2 3 = (0, 6)).
Check (eq_refl ((0, 6)) <: mulc 2 3 = (0, 6)).
Check (eq_refl ((0, 6)) <<: mulc 2 3 = (0, 6)).
Definition compute1 := Eval compute in mulc 2 3.
Check (eq_refl compute1 : (0, 6) = (0, 6)).

Check (eq_refl : mulc 9223372036854775807 2 = (1, 9223372036854775806)).
Check (eq_refl ((1, 9223372036854775806)) <: mulc 9223372036854775807 2 = (1, 9223372036854775806)).
Check (eq_refl ((1, 9223372036854775806)) <<: mulc 9223372036854775807 2 = (1, 9223372036854775806)).

Definition compute2 := Eval compute in mulc 9223372036854775807 2.
Check (eq_refl compute2 : (1, 9223372036854775806) = (1, 9223372036854775806)).

Check (eq_refl : mulc 0 0 = (0, 0)).
Check (eq_refl (0, 0) <: mulc 0 0 = (0, 0)).
Check (eq_refl ((0, 0)) <<: mulc 0 0 = (0, 0)).
