From Coq Require Import Cyclic31.

Definition Nat `(int31) := nat.
Definition Zero (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _: digits) := 0.

Check (eq_refl (int31_rect Nat Zero 1) : 0 = 0).
Check (eq_refl (int31_rect Nat Zero 1) <: 0 = 0).
Check (eq_refl (int31_rect Nat Zero 1) <<: 0 = 0).
