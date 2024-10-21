(* This file checks that operations over int63 are unsigned. *)
Require Import PrimInt63.

Open Scope uint63_scope.

(* (0-1) must be the maximum integer value and not negative 1 *)

Check (eq_refl : div 1 (sub 0 1) = 0).
Check (eq_refl 0 <: div 1 (sub 0 1) = 0).
Check (eq_refl 0 <<: div 1 (sub 0 1) = 0).
Definition compute1 := Eval compute in div 1 (sub 0 1).
Check (eq_refl compute1 : 0 = 0).

Check (eq_refl : mod 3 (sub 0 1) = 3).
Check (eq_refl 3 <: mod 3 (sub 0 1) = 3).
Check (eq_refl 3 <<: mod 3 (sub 0 1) = 3).
Definition compute2 := Eval compute in mod 3 (sub 0 1).
Check (eq_refl compute2 : 3 = 3).
