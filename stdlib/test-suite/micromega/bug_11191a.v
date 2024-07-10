From Stdlib Require Import ZArith Lia.

Goal forall p n, (0 < Z.pos (p ^ n))%Z.
  intros.
  lia.
Qed.
