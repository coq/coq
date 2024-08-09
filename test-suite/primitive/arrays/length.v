From Stdlib Require Import Uint63 PArray.

Open Scope uint63_scope.

Definition t : array nat := [| 1; 3; 2 | 4 |]%nat.
Definition foo1 := (eq_refl : PArray.length t = 3).
Definition foo2 := (eq_refl 3 <: PArray.length t = 3).
Definition foo3 := (eq_refl 3 <<: PArray.length t = 3).
Definition x1 := Eval compute in PArray.length t.
Definition foo4 := (eq_refl : x1 = 3).
Definition x2 := Eval cbn in PArray.length t.
Definition foo5 := (eq_refl : x2 = 3).
