Require Import ZArith Int63 Floats.

Check (eq_refl : ldexp one 9223372036854773807%Z = infinity).
Check (eq_refl infinity <: ldexp one 9223372036854773807%Z = infinity).
Check (eq_refl infinity <<: ldexp one 9223372036854773807%Z = infinity).

Check (eq_refl : ldshiftexp one 9223372036854775807 = infinity).
Check (eq_refl infinity <: ldshiftexp one 9223372036854775807 = infinity).
Check (eq_refl infinity <<: ldshiftexp one 9223372036854775807 = infinity).

Check (eq_refl : ldexp one (-2102) = 0%float).
Check (eq_refl 0%float <: ldexp one (-2102) = 0%float).
Check (eq_refl 0%float <<: ldexp one (-2102) = 0%float).

Check (eq_refl : ldexp one (-3) = 0.125%float).
Check (eq_refl 0.125%float <: ldexp one (-3) = 0.125%float).
Check (eq_refl 0.125%float <<: ldexp one (-3) = 0.125%float).

Check (eq_refl : ldexp one 3 = 8%float).
Check (eq_refl 8%float <: ldexp one 3 = 8%float).
Check (eq_refl 8%float <<: ldexp one 3 = 8%float).
