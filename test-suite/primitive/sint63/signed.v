(* This file checks that operations over sint63 are signed. *)
Require Import Sint63.

Open Scope sint63_scope.

(* (0-1) must be negative 1 and not the maximum integer value *)

Check (eq_refl : 1/(0-1) = -1).
Check (eq_refl (-1) <: 1/(0-1) = -1).
Check (eq_refl (-1) <<: 1/(0-1) = -1).
Definition compute1 := Eval compute in 1/(0-1).
Check (eq_refl compute1 : -1 = -1).

Check (eq_refl : 3 mod (0-1) = 0).
Check (eq_refl 0 <: 3 mod (0-1) = 0).
Check (eq_refl 0 <<: 3 mod (0-1) = 0).
Definition compute2 := Eval compute in 3 mod (0-1).
Check (eq_refl compute2 : 0 = 0).
