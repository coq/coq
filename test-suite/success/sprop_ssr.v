Set Allow StrictProp.

Require Import ssreflect.

Goal forall T : SProp, T -> True.
Proof.
  move=> T +.
  intros X;exact I.
Qed.
