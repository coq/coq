Require Import Int63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : diveucl 6 3 = (2,0)).
Check (eq_refl (2,0) <: diveucl 6 3 = (2,0)).
Check (eq_refl (2,0) <<: diveucl 6 3 = (2,0)).
Definition compute1 := Eval compute in diveucl 6 3.
Check (eq_refl compute1 : (2,0) = (2,0)).

Check (eq_refl : diveucl 5 3 = (1,2)).
Check (eq_refl (1,2) <: diveucl 5 3 = (1,2)).
Check (eq_refl (1,2) <<: diveucl 5 3 = (1,2)).
Definition compute2 := Eval compute in diveucl 5 3.
Check (eq_refl compute2 : (1,2) = (1,2)).
