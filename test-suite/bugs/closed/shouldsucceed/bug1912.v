Require Import ZArith.

Goal forall x, Zsucc (Zpred x) = x.
intros x.
omega.
Qed.
