From Stdlib Require Import BinInt.
Goal forall m n : Z, (m >= n)%Z -> (m >= m)%Z /\ (m >= n)%Z.
intros; intuition.
Show.
Abort.
