Class ORDER A := Order {
  LEQ : A -> A -> bool; 
  leqRefl: forall x, true = LEQ x x
}.

Section XXX.

Variable A:Type.
Variable (O:ORDER A).
Definition aLeqRefl := @leqRefl _ O.

Lemma OK : forall x, true = LEQ x x.
Proof.
  intros.
  unfold LEQ.
  destruct O.
  clear.
  Fail apply aLeqRefl.
Abort.
