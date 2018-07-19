Require Import ZArith Floats.

Definition two := Eval compute in (one + one)%float.
Definition half := Eval compute in (one / two)%float.
Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1022)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Check (eq_refl : valid_binary (Prim2SF zero) = true).
Check (eq_refl : valid_binary (Prim2SF neg_zero) = true).
Check (eq_refl : valid_binary (Prim2SF one) = true).
Check (eq_refl : valid_binary (Prim2SF (-one)) = true).
Check (eq_refl : valid_binary (Prim2SF infinity) = true).
Check (eq_refl : valid_binary (Prim2SF neg_infinity) = true).
Check (eq_refl : valid_binary (Prim2SF huge) = true).
Check (eq_refl : valid_binary (Prim2SF tiny) = true).
Check (eq_refl : valid_binary (Prim2SF denorm) = true).
Check (eq_refl : valid_binary (Prim2SF nan) = true).
Check (eq_refl : valid_binary (Prim2SF two) = true).
Check (eq_refl : valid_binary (Prim2SF half) = true).

Check (eq_refl true <: valid_binary (Prim2SF zero) = true).
Check (eq_refl true <: valid_binary (Prim2SF neg_zero) = true).
Check (eq_refl true <: valid_binary (Prim2SF one) = true).
Check (eq_refl true <: valid_binary (Prim2SF (-one)) = true).
Check (eq_refl true <: valid_binary (Prim2SF infinity) = true).
Check (eq_refl true <: valid_binary (Prim2SF neg_infinity) = true).
Check (eq_refl true <: valid_binary (Prim2SF huge) = true).
Check (eq_refl true <: valid_binary (Prim2SF tiny) = true).
Check (eq_refl true <: valid_binary (Prim2SF denorm) = true).
Check (eq_refl true <: valid_binary (Prim2SF nan) = true).
Check (eq_refl true <: valid_binary (Prim2SF two) = true).
Check (eq_refl true <: valid_binary (Prim2SF half) = true).
