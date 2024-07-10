From Stdlib Require Import ZArith Lia.

Goal forall p, (0 < Z.pos (p ^ 2))%Z.
  intros.
  lia.
Qed.
