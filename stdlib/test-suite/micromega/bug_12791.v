From Stdlib Require Import Lia.

Definition t := nat.

Goal forall (a b: t), let c := a in b = a -> b = c.
Proof.
  intros a b c H.
  lia.
Qed.
