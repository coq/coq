Require Import PrimInt63 PrimFloat.

Definition half := 0x1p-1%float.
Definition three_quarters := (half + 0x1p-2)%float.

Check (eq_refl : normfr_mantissa one = 0%uint63).
Check (eq_refl : normfr_mantissa half = (lsl 1 52)%uint63).
Check (eq_refl : normfr_mantissa (-half) = (lsl 1 52)%uint63).
Check (eq_refl : normfr_mantissa (-one) = 0%uint63).
Check (eq_refl : normfr_mantissa zero = 0%uint63).
Check (eq_refl : normfr_mantissa nan = 0%uint63).
Check (eq_refl : normfr_mantissa three_quarters = (lsl 3 51)%uint63).
