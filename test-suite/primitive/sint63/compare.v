Require Import Sint63.

Set Implicit Arguments.

Open Scope sint63_scope.

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

Check (eq_refl : 4611686018427387903 ?= 0 = Gt).
Check (eq_refl Gt <: 4611686018427387903 ?= 0 = Gt).
Check (eq_refl Gt <<: 4611686018427387903 ?= 0 = Gt).
Definition compute3 := Eval compute in 4611686018427387903 ?= 0.
Check (eq_refl compute3 : Gt = Gt).

Check (eq_refl : -1 ?= 1 = Lt).
Check (eq_refl Lt <: -1 ?= 1 = Lt).
Check (eq_refl Lt <<: -1 ?= 1 = Lt).
Definition compute4 := Eval compute in -1 ?= 1.
Check (eq_refl compute4 : Lt = Lt).

Check (eq_refl : 4611686018427387903 ?= -4611686018427387904 = Gt).
Check (eq_refl Gt <: 4611686018427387903 ?= -4611686018427387904 = Gt).
Check (eq_refl Gt <<: 4611686018427387903 ?= -4611686018427387904 = Gt).
Definition compute5 :=
  Eval compute in 4611686018427387903 ?= -4611686018427387904.
Check (eq_refl compute5 : Gt = Gt).
