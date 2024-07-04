Require Import BinNums PrimInt63 PrimFloat FloatOps.

Check (eq_refl : Z.ldexp one (Zpos (xI (xI (xI (xI (xO (xI (xO (xO (xO (xO (xO (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (* 9223372036854773807 *) = infinity).

Check (eq_refl : Z.ldexp one (Zneg (xO (xI (xI (xO (xI (xI (xO (xO (xO (xO (xO xH)))))))))))) (* -2102 *) = 0%float).

Check (eq_refl : Z.ldexp one (Zneg (xI xH)) (* -3 *) = 0.125%float).

Check (eq_refl : Z.ldexp one (Zpos (xI xH)) = 8%float).
