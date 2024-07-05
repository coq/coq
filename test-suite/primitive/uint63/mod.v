Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : mod 6 3 = 0).
Check (eq_refl 0 <: mod 6 3 = 0).
Check (eq_refl 0 <<: mod 6 3 = 0).
Definition compute1 := Eval compute in mod 6 3.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : mod 5 3 = 2).
Check (eq_refl 2 <: mod 5 3 = 2).
Check (eq_refl 2 <<: mod 5 3 = 2).
Definition compute2 := Eval compute in mod 5 3.
Check (eq_refl compute2 : 2 = 2).
