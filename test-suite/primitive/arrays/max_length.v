From Stdlib Require Import Uint63 PArray.

Open Scope uint63_scope.

Definition max_length := 4194303.

Definition foo1 := (eq_refl max_length : PArray.max_length = max_length).
Definition foo2 := (eq_refl max_length <: PArray.max_length = max_length).
Definition foo3 := (eq_refl max_length <<: PArray.max_length = max_length).
Definition max_length2 := Eval compute in PArray.max_length.
Definition foo4 := (eq_refl : max_length = max_length2).
Definition max_length3 := Eval cbn in PArray.max_length.
Definition foo5 := (eq_refl : max_length = max_length3).
