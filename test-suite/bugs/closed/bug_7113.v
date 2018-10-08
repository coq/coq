Require Import Program.Tactics.
Section visibility.

  (* used to anomaly *)
  Program Let Fixpoint ev' (n : nat) : bool := _.
  Next Obligation. exact true. Qed.

  Check ev'.
End visibility.
Fail Check ev'.
