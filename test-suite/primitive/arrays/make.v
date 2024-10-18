From Stdlib Require Import PrimInt63 PrimArray.

Open Scope array_scope.

(* Immediate values *)
Definition t1 : array nat := [| 3; 3; 3; 3 | 3 |].
Definition t2 := PrimArray.make 4 3.
Definition foo1 := (eq_refl : t1 = t2).
Definition foo2 := (eq_refl t1 <: t1 = t2).
Definition foo3 := (eq_refl t1 <<: t1 = t2).
Definition x1 := Eval compute in t2.
Definition foo4 := (eq_refl : x1 = t1).
Definition x2 := Eval cbn in t2.
Definition foo5 := (eq_refl : x2 = t1).

Definition partial1 := Eval lazy in @PrimArray.make.
Definition partial2 := Eval vm_compute in @PrimArray.make.
Definition partial3 := Eval native_compute in @PrimArray.make.
