Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 1 ?= 1 = Eq).
Check (eq_refl Eq <: 1 ?= 1 = Eq).
Check (eq_refl Eq <<: 1 ?= 1 = Eq).
Definition compute1 := Eval compute in 1 ?= 1.
Check (eq_refl compute1 : Eq = Eq).

Check (eq_refl : 1 ?= 2 = Lt).
Check (eq_refl Lt <: 1 ?= 2 = Lt).
Check (eq_refl Lt <<: 1 ?= 2 = Lt).
Definition compute2 := Eval compute in 1 ?= 2.
Check (eq_refl compute2 : Lt = Lt).

Check (eq_refl : 9223372036854775807 ?= 0 = Gt).
Check (eq_refl Gt <: 9223372036854775807 ?= 0 = Gt).
Check (eq_refl Gt <<: 9223372036854775807 ?= 0 = Gt).
Definition compute3 := Eval compute in 9223372036854775807 ?= 0.
Check (eq_refl compute3 : Gt = Gt).
