Require Import PrimInt63.

Set Implicit Arguments.

Open Scope uint63_scope.

Check (eq_refl : diveucl_21 1 1 2 = (4611686018427387904,1)).
Check (eq_refl (4611686018427387904,1) <: diveucl_21 1 1 2 = (4611686018427387904,1)).
Check (eq_refl (4611686018427387904,1) <<: diveucl_21 1 1 2 = (4611686018427387904,1)).
Definition compute1 := Eval compute in diveucl_21 1 1 2.
Check (eq_refl compute1 : (4611686018427387904,1) = (4611686018427387904,1)).

Check (eq_refl : diveucl_21 3 1 2 = (0, 0)).
Check (eq_refl (0, 0) <: diveucl_21 3 1 2 = (0, 0)).
Check (eq_refl (0, 0) <<: diveucl_21 3 1 2 = (0, 0)).
Definition compute2 := Eval compute in diveucl_21 3 1 2.
Check (eq_refl compute2 : (0, 0) = (0, 0)).

Check (eq_refl : diveucl_21 1 1 0 = (0,0)).
Check (eq_refl (0,0) <: diveucl_21 1 1 0 = (0,0)).
Check (eq_refl (0,0) <<: diveucl_21 1 1 0 = (0,0)).

Check (eq_refl : diveucl_21 9223372036854775807 0 1 = (0,0)).
Check (eq_refl (0,0) <: diveucl_21 9223372036854775807 0 1 = (0,0)).
Check (eq_refl (0,0) <<: diveucl_21 9223372036854775807 0 1 = (0,0)).

Check (eq_refl : diveucl_21 9305446873517 1793572051078448654 4930380657631323783 = (17407905077428, 3068214991893055266)).
Check (eq_refl (17407905077428, 3068214991893055266) <: diveucl_21 9305446873517 1793572051078448654 4930380657631323783 = (17407905077428, 3068214991893055266)).
Check (eq_refl (17407905077428, 3068214991893055266) <<: diveucl_21 9305446873517 1793572051078448654 4930380657631323783 = (17407905077428, 3068214991893055266)).
