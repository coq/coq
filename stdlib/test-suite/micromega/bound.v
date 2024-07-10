From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Unset Lia Cache.

Goal forall x y z, 2 <= x ->
               3 <= x*y ->
               4 <= x*y*z ->
               4^10 <= (x^3*y^2*z)^10.
Proof.
  intros.
  cbn.
  Timeout 10 lia. (* runs forever in 8.15, < 1s *)
Qed.

Goal forall x, -3 <= x ->
               (-3)^3 <= x^3.
Proof.
  intros.
  Fail lia.
  (* but, interval analysis could conclude because the exponent is odd. *)
  (* A proof with an explicit case-split *)
  assert (0 <= x \/ x <= 0) by lia.
  destruct H0.
  lia.
  assert ( (-x)^3 <= 3^3).
  { apply Z.pow_le_mono_l. lia. }
  lia.
Qed.
