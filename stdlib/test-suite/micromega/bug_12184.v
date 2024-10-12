Require Import Lia.
Require Import ZArith.

Goal forall p : positive, (0 < Z.pos (2^p)%positive)%Z.
Proof.
  intros p.
  lia.
Qed.
