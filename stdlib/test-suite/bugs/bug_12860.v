Require Import Stdlib.nsatz.NsatzTactic.
Require Import Stdlib.ZArith.ZArith Stdlib.QArith.QArith.

Goal forall x y : Z, (x + y = y + x)%Z.
  intros; nsatz.
Qed.

Goal forall x y : Q, Qeq (x + y) (y + x).
  intros; nsatz.
Qed.
