(* This file checks that operations over int63 are unsigned. *)
Require Import Int63.

Open Scope int63_scope.

(* (0-1) must be the maximum integer value and not negative 1 *)

Check (eq_refl : 1/(0-1) = 0).
Check (eq_refl 0 <: 1/(0-1) = 0).
Check (eq_refl 0 <<: 1/(0-1) = 0).
Definition compute1 := Eval compute in 1/(0-1).
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : 3 \% (0-1) = 3).
Check (eq_refl 3 <: 3 \% (0-1) = 3).
Check (eq_refl 3 <<: 3 \% (0-1) = 3).
Definition compute2 := Eval compute in 3 \% (0-1).
Check (eq_refl compute2 : 3 = 3).
