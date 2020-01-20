Require Import ZArith Lia.

Goal forall p, (0 < Z.pos (p ^ 2))%Z.
  intros.
  lia.
Qed.

Goal forall p n, (0 < Z.pos (p ^ n))%Z.
  intros.
  lia.
Qed.
