From Stdlib Require Import Lia.
Unset Lia Cache.
Definition t := nat.
Goal forall (n : t), n = n.
Proof.
  intros.
  lia.
Qed.
Goal let t' := nat in forall (n : t'), n = n.
Proof.
  intros.
  lia.
Qed.
