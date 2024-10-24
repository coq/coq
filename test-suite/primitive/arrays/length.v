From Stdlib Require Import PrimInt63 PrimArray.

Open Scope uint63_scope.

Definition t : array nat := [| 1; 3; 2 | 4 |]%nat.
Definition foo1 := (eq_refl : PrimArray.length t = 3).
Definition foo2 := (eq_refl 3 <: PrimArray.length t = 3).
Definition foo3 := (eq_refl 3 <<: PrimArray.length t = 3).
Definition x1 := Eval compute in PrimArray.length t.
Definition foo4 := (eq_refl : x1 = 3).
Definition x2 := Eval cbn in PrimArray.length t.
Definition foo5 := (eq_refl : x2 = 3).
