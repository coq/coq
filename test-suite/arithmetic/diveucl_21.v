Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : diveucl_21 1 1 2 = (4611686018427387904,1)).
Check (eq_refl (4611686018427387904,1) <: diveucl_21 1 1 2 = (4611686018427387904,1)).
Check (eq_refl (4611686018427387904,1) <<: diveucl_21 1 1 2 = (4611686018427387904,1)).
Definition compute1 := Eval compute in diveucl_21 1 1 2.
Check (eq_refl compute1 : (4611686018427387904,1) = (4611686018427387904,1)).

Check (eq_refl : diveucl_21 3 1 2 = (4611686018427387904, 1)).
Check (eq_refl (4611686018427387904, 1) <: diveucl_21 3 1 2 = (4611686018427387904, 1)).
Check (eq_refl (4611686018427387904, 1) <<: diveucl_21 3 1 2 = (4611686018427387904, 1)).
Definition compute2 := Eval compute in diveucl_21 3 1 2.
Check (eq_refl compute2 : (4611686018427387904, 1) = (4611686018427387904, 1)).
