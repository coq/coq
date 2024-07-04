Require Import PrimFloat.

Open Scope float_scope.

Check (eq_refl : next_up nan = nan).
Check (eq_refl : next_down nan = nan).
Check (eq_refl : next_up neg_infinity = -0x1.fffffffffffffp+1023).
Check (eq_refl : next_down neg_infinity = neg_infinity).
Check (eq_refl : next_up (-0x1.fffffffffffffp+1023) = -0x1.ffffffffffffep+1023).
Check (eq_refl : next_down (-0x1.fffffffffffffp+1023) = neg_infinity).
Check (eq_refl : next_up (-0x1.ffffffffffffap+1023) = -0x1.ffffffffffff9p+1023).
Check (eq_refl : next_down (-0x1.ffffffffffffap+1023) = -0x1.ffffffffffffbp+1023).
Check (eq_refl : next_up (-0x1.fffffffffffff) = -0x1.ffffffffffffe).
Check (eq_refl : next_down (-0x1.fffffffffffff) = -0x1p+1).
Check (eq_refl : next_up (-0x1p1) = -0x1.fffffffffffff).
Check (eq_refl : next_down (-0x1p1) = -0x1.0000000000001p+1).
Check (eq_refl : next_up (-0) = 0x0.0000000000001p-1022).
Check (eq_refl : next_down (-0) = -0x0.0000000000001p-1022).
Check (eq_refl : next_up 0 = 0x0.0000000000001p-1022).
Check (eq_refl : next_down 0 = -0x0.0000000000001p-1022).
Check (eq_refl : next_up 0x1p1 = 0x1.0000000000001p+1).
Check (eq_refl : next_down 0x1p1 = 0x1.fffffffffffff).
Check (eq_refl : next_up 0x1.fffffffffffff = 0x1p+1).
Check (eq_refl : next_down 0x1.fffffffffffff = 0x1.ffffffffffffe).
Check (eq_refl : next_up 0x1.fffffffffffffp+1023 = infinity).
Check (eq_refl : next_down 0x1.fffffffffffffp+1023 = 0x1.ffffffffffffep+1023).
Check (eq_refl : next_up infinity = infinity).
Check (eq_refl : next_down infinity = 0x1.fffffffffffffp+1023).
