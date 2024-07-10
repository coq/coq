From Stdlib Require Import Lia ZArith.

Goal forall x, Z.succ (Z.pred x) = x.
intros x.
lia.
Qed.
