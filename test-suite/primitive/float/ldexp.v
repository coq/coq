Require Import ZArith Uint63 Floats.

Check (eq_refl : Z.ldexp one 9223372036854773807%Z = infinity).

Check (eq_refl : ldshiftexp one 9223372036854775807 = infinity).

Check (eq_refl : Z.ldexp one (-2102) = 0%float).

Check (eq_refl : Z.ldexp one (-3) = 0.125%float).

Check (eq_refl : Z.ldexp one 3 = 8%float).
