Ltac foo := idtac.
Ltac bar H := idtac.

Goal True.
Proof.
  Fail foo H.
  Fail foo H H'.
  Fail bar H H'.
  Fail bar H H' H''.
Abort.
