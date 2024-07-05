Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : lsl 3 61 = 6917529027641081856).
Check (eq_refl 6917529027641081856 <: lsl 3 61 = 6917529027641081856).
Check (eq_refl 6917529027641081856 <<: lsl 3 61 = 6917529027641081856).
Definition compute1 := Eval compute in lsl 3 61.
Check (eq_refl compute1 : 6917529027641081856 = 6917529027641081856).

Check (eq_refl : lsl 2 62 = 0).
Check (eq_refl 0 <: lsl 2 62 = 0).
Check (eq_refl 0 <<: lsl 2 62 = 0).
Definition compute2 := Eval compute in lsl 2 62.
Check (eq_refl compute2 : 0 = 0).

Check (eq_refl : lsl 9223372036854775807 64 = 0).
Check (eq_refl 0 <: lsl 9223372036854775807 64 = 0).
Check (eq_refl 0 <<: lsl 9223372036854775807 64 = 0).
Definition compute3 := Eval compute in lsl 9223372036854775807 64.
Check (eq_refl compute3 : 0 = 0).
