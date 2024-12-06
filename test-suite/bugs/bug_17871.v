Require Import PrimFloat.

Definition foo : { x : float | x = 1%float }.
Proof.
eexists.
Set Printing All.
native_compute.
(* was giving
@eq 0x0.05555897461p-1022%float 0x0.05555897461p-1022%float 0x1p+0%float *)
Abort.

Definition foo x y : ((x =? 0.0) = (y =? 0.0))%float.
Proof.
native_cast_no_check (eq_refl (x =? 0.0))%float.
Fail Defined.
Abort.

(* the above was succeeding allowing
Goal False.
Proof. now generalize (foo 0.0 1.0). Qed.
*)
