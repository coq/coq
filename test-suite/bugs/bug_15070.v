Require Import PrimArray PrimFloat PrimInt63.

Goal False.
Proof.
set (f := fun x => get (set (make 2 one) 1 x) 1).
generalize (eq_refl (f zero)).
change (f zero = zero -> False).
intros H0.
generalize (eq_refl f) (eq_refl f).
generalize f at 1 3.
intros g H1.
vm_compute.
rewrite H1.
intros H2.
revert H0.
rewrite H2.
intros H3.
apply (f_equal classify) in H3.
revert H3.
vm_compute.
Fail discriminate.
Abort.
