Require Import Cyclic63.

Set Implicit Arguments.

Open Scope int63_scope.

Check (eq_refl : 2 *c 3 = WW 0 6).
Check (eq_refl (WW 0 6) <: 2 *c 3 = WW 0 6).
Check (eq_refl (WW 0 6) <<: 2 *c 3 = WW 0 6).
Definition compute1 := Eval compute in 2 *c 3.
Check (eq_refl compute1 : WW 0 6 = WW 0 6).

Check (eq_refl : 9223372036854775807 *c 2 = WW 1 9223372036854775806).
Check (eq_refl (WW 1 9223372036854775806) <: 9223372036854775807 *c 2 = WW 1 9223372036854775806).
Check (eq_refl (WW 1 9223372036854775806) <<: 9223372036854775807 *c 2 = WW 1 9223372036854775806).

Definition compute2 := Eval compute in 9223372036854775807 *c 2.
Check (eq_refl compute2 : WW 1 9223372036854775806 = WW 1 9223372036854775806).

Check (eq_refl : 0 *c 0 = W0).
Check (eq_refl (@W0 int) <: 0 *c 0 = W0).
Check (eq_refl (@W0 int) <<: 0 *c 0 = W0).
