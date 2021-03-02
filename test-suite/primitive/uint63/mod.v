Require Import Uint63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : 6 mod 3 = 0).
Check (eq_refl 0 <: 6 mod 3 = 0).
Check (eq_refl 0 <<: 6 mod 3 = 0).
Definition compute1 := Eval compute in 6 mod 3.
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : 5 mod 3 = 2).
Check (eq_refl 2 <: 5 mod 3 = 2).
Check (eq_refl 2 <<: 5 mod 3 = 2).
Definition compute2 := Eval compute in 5 mod 3.
Check (eq_refl compute2 : 2 = 2).
