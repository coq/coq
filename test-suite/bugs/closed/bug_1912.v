Require Import Omega.

Goal forall x, Z.succ (Z.pred x) = x.
intros x.
omega.
Qed.
