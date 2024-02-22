Check True.
Goal True /\ True.
  Check True.
  1:Check True.
  1: idtac.
  1:{ admit. }
Abort.

Require Import Ltac2.Ltac2.

Check True.
Goal True /\ True.
  Check True.
  1:Check True.
  1: ().
  1:{ admit. }
Abort.
