From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Set Info Micromega.

Goal forall (x y z:R), x + y > 0 ->  x - y > 0 -> x + z = 0 -> x < 0 -> False.
Proof.
  intros.
  lra.
Qed.

Goal forall (x y z:R), x + y > 0 ->  x - y > 0 -> x + z = 0 -> x < 0 -> False.
Proof.
  intros.
  clear - H2 H0 H.
  lra.
Qed.
