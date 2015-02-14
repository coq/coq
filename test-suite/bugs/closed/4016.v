Require Import Setoid.

Parameter eq : relation nat.
Declare Instance Equivalence_eq : Equivalence eq.

Lemma foo : forall z, eq z 0 -> forall x, eq x 0 -> eq z x.
Proof.
intros z Hz x Hx.
rewrite <- Hx in Hz.
destruct z.
Abort.

