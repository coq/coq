Require Import ZArith Floats.

Definition two := Eval compute in (one + one)%float.
Definition half := Eval compute in (one / two)%float.
Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Check (eq_refl : SF2Prim (Prim2SF zero) = zero).
Check (eq_refl : SF2Prim (Prim2SF neg_zero) = neg_zero).
Check (eq_refl : SF2Prim (Prim2SF one) = one).
Check (eq_refl : SF2Prim (Prim2SF (-one)) = (-one)%float).
Check (eq_refl : SF2Prim (Prim2SF infinity) = infinity).
Check (eq_refl : SF2Prim (Prim2SF neg_infinity) = neg_infinity).
Check (eq_refl : SF2Prim (Prim2SF huge) = huge).
Check (eq_refl : SF2Prim (Prim2SF tiny) = tiny).
Check (eq_refl : SF2Prim (Prim2SF denorm) = denorm).
Check (eq_refl : SF2Prim (Prim2SF nan) = nan).
Check (eq_refl : SF2Prim (Prim2SF two) = two).
Check (eq_refl : SF2Prim (Prim2SF half) = half).
