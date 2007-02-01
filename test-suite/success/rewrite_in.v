Require Import Setoid.

Goal forall (P Q : Prop) (f:P->Prop) (p:P), (P<->Q) -> f p -> True.
  intros P Q f p H.
  rewrite H in p || trivial.
Qed.


