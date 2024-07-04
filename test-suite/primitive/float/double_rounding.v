Require Import PrimFloat.

(* This test check that there is no double rounding with 80 bits registers inside float computations *)

Definition big_vm := 0x1p+53%float.  (* Z.ldexp one 53%Z *)
Definition small_vm := Eval vm_compute in (one + 0x1p-52)%float.
Definition result_vm := Eval vm_compute in (big_vm + small_vm)%float.
Definition check_vm := Eval vm_compute in (big_vm + one)%float.

Check (eq_refl : (result_vm ?= big_vm)%float = FGt).
Check (eq_refl : (check_vm ?= big_vm)%float = FEq).
