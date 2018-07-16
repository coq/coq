Require Import Floats ZArith.

(* This test check that there is no double rounding with 80 bits registers inside float computations *)

Definition big_cbn := Eval cbn in ldexp one (53)%Z.
Definition small_cbn := Eval cbn in (one + ldexp one (-52)%Z)%float.
Definition result_cbn := Eval cbn in (big_cbn + small_cbn)%float.
Definition check_cbn := Eval cbn in (big_cbn + one)%float.

Check (eq_refl : (result_cbn ?= big_cbn)%float = Some Gt).
Check (eq_refl : (check_cbn ?= big_cbn)%float = Some Eq).


Definition big_cbv := Eval cbv in ldexp one (53)%Z.
Definition small_cbv := Eval cbv in (one + ldexp one (-52)%Z)%float.
Definition result_cbv := Eval cbv in (big_cbv + small_cbv)%float.
Definition check_cbv := Eval cbv in (big_cbv + one)%float.

Check (eq_refl : (result_cbv ?= big_cbv)%float = Some Gt).
Check (eq_refl : (check_cbv ?= big_cbv)%float = Some Eq).
