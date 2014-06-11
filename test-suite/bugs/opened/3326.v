Class ORDER A := Order {
  LEQ : A -> A -> bool;
  leqRefl: forall x, true = LEQ x x
}.

Section XXX.

Variable A:Type.
Variable (O:ORDER A).
Definition aLeqRefl := @leqRefl _ O.

Lemma OK : forall x, true = LEQ x x.
  intros.
  unfold LEQ.
  destruct O.
  clear.
  Fail apply aLeqRefl. (* Toplevel input, characters 15-30:
Anomaly: Uncaught exception Not_found(_). Please report. *)
