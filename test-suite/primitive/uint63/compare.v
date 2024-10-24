Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : compare 1 1 = Eq).
Check (eq_refl Eq <: compare 1 1 = Eq).
Check (eq_refl Eq <<: compare 1 1 = Eq).
Definition compute1 := Eval compute in compare 1 1.
Check (eq_refl compute1 : Eq = Eq).

Check (eq_refl : compare 1 2 = Lt).
Check (eq_refl Lt <: compare 1 2 = Lt).
Check (eq_refl Lt <<: compare 1 2 = Lt).
Definition compute2 := Eval compute in compare 1 2.
Check (eq_refl compute2 : Lt = Lt).

Check (eq_refl : compare 9223372036854775807 0 = Gt).
Check (eq_refl Gt <: compare 9223372036854775807 0 = Gt).
Check (eq_refl Gt <<: compare 9223372036854775807 0 = Gt).
Definition compute3 := Eval compute in compare 9223372036854775807 0.
Check (eq_refl compute3 : Gt = Gt).
