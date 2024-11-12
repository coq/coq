Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : div 6 3 = 2).
Check (eq_refl 2 <: div 6 3 = 2).
Check (eq_refl 2 <<: div 6 3 = 2).
Definition compute1 := Eval compute in div 6 3.
Check (eq_refl compute1 : 2 = 2).

Check (eq_refl : div 3 2 = 1).
Check (eq_refl 1 <: div 3 2 = 1).
Check (eq_refl 1 <<: div 3 2 = 1).
Definition compute2 := Eval compute in div 3 2.
Check (eq_refl compute2 : 1 = 1).
