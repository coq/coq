Require Import ZArith Int63 Floats.

Open Scope float_scope.

Definition f0 := zero.
Definition f1 := neg_zero.
Definition f2 := Eval compute in ldexp one 0.
Definition f3 := Eval compute in -f1.
(* smallest positive float *)
Definition f4 := Eval compute in ldexp one (-1074).
Definition f5 := Eval compute in -f3.
Definition f6 := infinity.
Definition f7 := neg_infinity.
Definition f8 := Eval compute in ldexp one (-1).
Definition f9 := Eval compute in -f8.
Definition f10 := Eval compute in of_int63 42.
Definition f11 := Eval compute in -f10.
(* max float *)
Definition f12 := Eval compute in ldexp (of_int63 9007199254740991) 1024.
Definition f13 := Eval compute in -f12.
(* smallest positive normalized float *)
Definition f14 := Eval compute in ldexp one (-1022).
Definition f15 := Eval compute in -f14.

Check (eq_refl : Prim2SF (next_up f0) = SF64succ (Prim2SF f0)).
Check (eq_refl : Prim2SF (next_down f0) = SF64pred (Prim2SF f0)).
Check (eq_refl : Prim2SF (next_up f1) = SF64succ (Prim2SF f1)).
Check (eq_refl : Prim2SF (next_down f1) = SF64pred (Prim2SF f1)).
Check (eq_refl : Prim2SF (next_up f2) = SF64succ (Prim2SF f2)).
Check (eq_refl : Prim2SF (next_down f2) = SF64pred (Prim2SF f2)).
Check (eq_refl : Prim2SF (next_up f3) = SF64succ (Prim2SF f3)).
Check (eq_refl : Prim2SF (next_down f3) = SF64pred (Prim2SF f3)).
Check (eq_refl : Prim2SF (next_up f4) = SF64succ (Prim2SF f4)).
Check (eq_refl : Prim2SF (next_down f4) = SF64pred (Prim2SF f4)).
Check (eq_refl : Prim2SF (next_up f5) = SF64succ (Prim2SF f5)).
Check (eq_refl : Prim2SF (next_down f5) = SF64pred (Prim2SF f5)).
Check (eq_refl : Prim2SF (next_up f6) = SF64succ (Prim2SF f6)).
Check (eq_refl : Prim2SF (next_down f6) = SF64pred (Prim2SF f6)).
Check (eq_refl : Prim2SF (next_up f7) = SF64succ (Prim2SF f7)).
Check (eq_refl : Prim2SF (next_down f7) = SF64pred (Prim2SF f7)).
Check (eq_refl : Prim2SF (next_up f8) = SF64succ (Prim2SF f8)).
Check (eq_refl : Prim2SF (next_down f8) = SF64pred (Prim2SF f8)).
Check (eq_refl : Prim2SF (next_up f9) = SF64succ (Prim2SF f9)).
Check (eq_refl : Prim2SF (next_down f9) = SF64pred (Prim2SF f9)).
Check (eq_refl : Prim2SF (next_up f10) = SF64succ (Prim2SF f10)).
Check (eq_refl : Prim2SF (next_down f10) = SF64pred (Prim2SF f10)).
Check (eq_refl : Prim2SF (next_up f11) = SF64succ (Prim2SF f11)).
Check (eq_refl : Prim2SF (next_down f11) = SF64pred (Prim2SF f11)).
Check (eq_refl : Prim2SF (next_up f12) = SF64succ (Prim2SF f12)).
Check (eq_refl : Prim2SF (next_down f12) = SF64pred (Prim2SF f12)).
Check (eq_refl : Prim2SF (next_up f13) = SF64succ (Prim2SF f13)).
Check (eq_refl : Prim2SF (next_down f13) = SF64pred (Prim2SF f13)).
Check (eq_refl : Prim2SF (next_up f14) = SF64succ (Prim2SF f14)).
Check (eq_refl : Prim2SF (next_down f14) = SF64pred (Prim2SF f14)).
Check (eq_refl : Prim2SF (next_up f15) = SF64succ (Prim2SF f15)).
Check (eq_refl : Prim2SF (next_down f15) = SF64pred (Prim2SF f15)).

Check (eq_refl (SF64succ (Prim2SF f0)) <: Prim2SF (next_up f0) = SF64succ (Prim2SF f0)).
Check (eq_refl (SF64pred (Prim2SF f0)) <: Prim2SF (next_down f0) = SF64pred (Prim2SF f0)).
Check (eq_refl (SF64succ (Prim2SF f1)) <: Prim2SF (next_up f1) = SF64succ (Prim2SF f1)).
Check (eq_refl (SF64pred (Prim2SF f1)) <: Prim2SF (next_down f1) = SF64pred (Prim2SF f1)).
Check (eq_refl (SF64succ (Prim2SF f2)) <: Prim2SF (next_up f2) = SF64succ (Prim2SF f2)).
Check (eq_refl (SF64pred (Prim2SF f2)) <: Prim2SF (next_down f2) = SF64pred (Prim2SF f2)).
Check (eq_refl (SF64succ (Prim2SF f3)) <: Prim2SF (next_up f3) = SF64succ (Prim2SF f3)).
Check (eq_refl (SF64pred (Prim2SF f3)) <: Prim2SF (next_down f3) = SF64pred (Prim2SF f3)).
Check (eq_refl (SF64succ (Prim2SF f4)) <: Prim2SF (next_up f4) = SF64succ (Prim2SF f4)).
Check (eq_refl (SF64pred (Prim2SF f4)) <: Prim2SF (next_down f4) = SF64pred (Prim2SF f4)).
Check (eq_refl (SF64succ (Prim2SF f5)) <: Prim2SF (next_up f5) = SF64succ (Prim2SF f5)).
Check (eq_refl (SF64pred (Prim2SF f5)) <: Prim2SF (next_down f5) = SF64pred (Prim2SF f5)).
Check (eq_refl (SF64succ (Prim2SF f6)) <: Prim2SF (next_up f6) = SF64succ (Prim2SF f6)).
Check (eq_refl (SF64pred (Prim2SF f6)) <: Prim2SF (next_down f6) = SF64pred (Prim2SF f6)).
Check (eq_refl (SF64succ (Prim2SF f7)) <: Prim2SF (next_up f7) = SF64succ (Prim2SF f7)).
Check (eq_refl (SF64pred (Prim2SF f7)) <: Prim2SF (next_down f7) = SF64pred (Prim2SF f7)).
Check (eq_refl (SF64succ (Prim2SF f8)) <: Prim2SF (next_up f8) = SF64succ (Prim2SF f8)).
Check (eq_refl (SF64pred (Prim2SF f8)) <: Prim2SF (next_down f8) = SF64pred (Prim2SF f8)).
Check (eq_refl (SF64succ (Prim2SF f9)) <: Prim2SF (next_up f9) = SF64succ (Prim2SF f9)).
Check (eq_refl (SF64pred (Prim2SF f9)) <: Prim2SF (next_down f9) = SF64pred (Prim2SF f9)).
Check (eq_refl (SF64succ (Prim2SF f10)) <: Prim2SF (next_up f10) = SF64succ (Prim2SF f10)).
Check (eq_refl (SF64pred (Prim2SF f10)) <: Prim2SF (next_down f10) = SF64pred (Prim2SF f10)).
Check (eq_refl (SF64succ (Prim2SF f11)) <: Prim2SF (next_up f11) = SF64succ (Prim2SF f11)).
Check (eq_refl (SF64pred (Prim2SF f11)) <: Prim2SF (next_down f11) = SF64pred (Prim2SF f11)).
Check (eq_refl (SF64succ (Prim2SF f12)) <: Prim2SF (next_up f12) = SF64succ (Prim2SF f12)).
Check (eq_refl (SF64pred (Prim2SF f12)) <: Prim2SF (next_down f12) = SF64pred (Prim2SF f12)).
Check (eq_refl (SF64succ (Prim2SF f13)) <: Prim2SF (next_up f13) = SF64succ (Prim2SF f13)).
Check (eq_refl (SF64pred (Prim2SF f13)) <: Prim2SF (next_down f13) = SF64pred (Prim2SF f13)).
Check (eq_refl (SF64succ (Prim2SF f14)) <: Prim2SF (next_up f14) = SF64succ (Prim2SF f14)).
Check (eq_refl (SF64pred (Prim2SF f14)) <: Prim2SF (next_down f14) = SF64pred (Prim2SF f14)).
Check (eq_refl (SF64succ (Prim2SF f15)) <: Prim2SF (next_up f15) = SF64succ (Prim2SF f15)).
Check (eq_refl (SF64pred (Prim2SF f15)) <: Prim2SF (next_down f15) = SF64pred (Prim2SF f15)).
