From Stdlib Require Import PrimInt63 PrimArray.

Definition t : array nat := [| 1; 3; 2 | 4 |].
Definition foo1 := (eq_refl : default t = 4).
Definition foo2 := (eq_refl 4 <: default t = 4).
Definition foo3 := (eq_refl 4 <<: default t = 4).
Definition x1 := Eval compute in default t.
Definition foo4 := (eq_refl : x1 = 4).
Definition x2 := Eval cbn in default t.
Definition foo5 := (eq_refl : x2 = 4).
