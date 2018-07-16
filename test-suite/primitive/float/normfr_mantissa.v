Require Import Int63 ZArith Floats.

Definition half := ldexp one (-1)%Z.
Definition three_quarters := (half + (ldexp one (-2)%Z))%float.

Check (eq_refl : normfr_mantissa one = 0%int63).
Check (eq_refl : normfr_mantissa half = (1 << 52)%int63).
Check (eq_refl : normfr_mantissa (-half) = (1 << 52)%int63).
Check (eq_refl : normfr_mantissa (-one) = 0%int63).
Check (eq_refl : normfr_mantissa zero = 0%int63).
Check (eq_refl : normfr_mantissa nan = 0%int63).
Check (eq_refl : normfr_mantissa three_quarters = (3 << 51)%int63).
