Require Import ZArith Floats.

Definition epsilon := Eval compute in Z.ldexp one (-1024)%Z.

Check (eq_refl : classify one = PNormal).
Check (eq_refl : classify (- one)%float = NNormal).
Check (eq_refl : classify epsilon = PSubn).
Check (eq_refl : classify (- epsilon)%float = NSubn).
Check (eq_refl : classify zero = PZero).
Check (eq_refl : classify neg_zero = NZero).
Check (eq_refl : classify infinity = PInf).
Check (eq_refl : classify neg_infinity = NInf).
Check (eq_refl : classify nan = NaN).
