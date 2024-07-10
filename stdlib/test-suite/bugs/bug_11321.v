From Stdlib Require Import Cyclic63.

Goal False.
Proof.
assert (4294967296 *c 2147483648 = WW 2 0)%uint63 as H.
  vm_cast_no_check (@eq_refl (zn2z int) (WW 2 0)%uint63).
generalize (f_equal (zn2z_to_Z wB to_Z) H).
now rewrite mulc_WW_spec.
Fail Qed.
Abort.
