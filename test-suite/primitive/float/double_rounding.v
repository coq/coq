Require Import Floats ZArith.

(* This test check that there is no double rounding with 80 bits registers inside float computations *)

Definition big_cbn := Eval cbn in ldexp one (53)%Z.
Definition small_cbn := Eval cbn in (one + ldexp one (-52)%Z)%float.
Definition result_cbn := Eval cbn in (big_cbn + small_cbn)%float.
Definition check_cbn := Eval cbn in (big_cbn + one)%float.

Check (eq_refl : (result_cbn ?= big_cbn)%float = FGt).
Check (eq_refl : (check_cbn ?= big_cbn)%float = FEq).


Definition big_cbv := Eval cbv in ldexp one (53)%Z.
Definition small_cbv := Eval cbv in (one + ldexp one (-52)%Z)%float.
Definition result_cbv := Eval cbv in (big_cbv + small_cbv)%float.
Definition check_cbv := Eval cbv in (big_cbv + one)%float.

Check (eq_refl : (result_cbv ?= big_cbv)%float = FGt).
Check (eq_refl : (check_cbv ?= big_cbv)%float = FEq).


Definition big_vm := Eval vm_compute in ldexp one (53)%Z.
Definition small_vm := Eval vm_compute in (one + ldexp one (-52)%Z)%float.
Definition result_vm := Eval vm_compute in (big_vm + small_vm)%float.
Definition check_vm := Eval vm_compute in (big_vm + one)%float.

Check (eq_refl : (result_vm ?= big_vm)%float = FGt).
Check (eq_refl : (check_vm ?= big_vm)%float = FEq).


Definition big_native := Eval native_compute in ldexp one (53)%Z.
Definition small_native := Eval native_compute in (one + ldexp one (-52)%Z)%float.
Definition result_native := Eval native_compute in (big_native + small_native)%float.
Definition check_native := Eval native_compute in (big_native + one)%float.

Check (eq_refl : (result_native ?= big_native)%float = FGt).
Check (eq_refl : (check_native ?= big_native)%float = FEq).
