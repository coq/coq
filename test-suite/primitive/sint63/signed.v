(* This file checks that operations over sint63 are signed. *)
Require Import TestSuite.sint63.

Open Scope sint63_scope.

(* (0-1) must be negative 1 and not the maximum integer value *)

Check (eq_refl : divs 1 (sub 0 1) = -1).
Check (eq_refl (-1) <: divs 1 (sub 0 1) = -1).
Check (eq_refl (-1) <<: divs 1 (sub 0 1) = -1).
Definition compute1 := Eval compute in divs 1 (sub 0 1).
Check (eq_refl compute1 : -1 = -1).

Check (eq_refl : mods 3 (sub 0 1) = 0).
Check (eq_refl 0 <: mods 3 (sub 0 1) = 0).
Check (eq_refl 0 <<: mods 3 (sub 0 1) = 0).
Definition compute2 := Eval compute in mods 3 (sub 0 1).
Check (eq_refl compute2 : 0 = 0).
