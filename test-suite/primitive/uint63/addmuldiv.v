Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : addmuldiv 32 3 5629499534213120 = 12887523328).
Check (eq_refl 12887523328 <: addmuldiv 32 3 5629499534213120 = 12887523328).
Check (eq_refl 12887523328 <<: addmuldiv 32 3 5629499534213120 = 12887523328).

Definition compute2 := Eval compute in addmuldiv 32 3 5629499534213120.
Check (eq_refl compute2 : 12887523328 = 12887523328).

Check (eq_refl : addmuldiv 0 256 9223372036854775807 = 256).
Check (eq_refl 256 <: addmuldiv 0 256 9223372036854775807 = 256).
Check (eq_refl 256 <<: addmuldiv 0 256 9223372036854775807 = 256).

Check (eq_refl : addmuldiv 63 9223372036854775807 256 = 256).
Check (eq_refl 256 <: addmuldiv 63 9223372036854775807 256 = 256).
Check (eq_refl 256 <<: addmuldiv 63 9223372036854775807 256 = 256).

Check (eq_refl : addmuldiv 65536 9223372036854775807 9223372036854775807 = 0).
Check (eq_refl 0 <: addmuldiv 65536 9223372036854775807 9223372036854775807 = 0).
Check (eq_refl 0 <<: addmuldiv 65536 9223372036854775807 9223372036854775807 = 0).
