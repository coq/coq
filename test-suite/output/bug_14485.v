From Ltac2 Require Import Ltac2.
Goal True.
  Fail unfold &unknown_identifier.
  Fail unfold &unknown_identifier at 1.
  exact I.
Qed.
