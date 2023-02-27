Require Import Program.Tactics.

Program Definition foo : nat := _.

Program Definition bar : nat * nat := (_, _).

Final Obligation.
  exact 0.
Fail Defined.
Abort.

Next Obligation.
  exact 0.
Defined.

Final Obligation.
  exact 1.
  Fail Defined.
Abort.

Final Obligation of bar.
  exact 1.
Defined.

Final Obligation.
  exact 2.
Defined.

Obligation Tactic := try constructor.

Program Definition baz := _ : _.

Final Obligation.
  exact True.
Defined.

Obligation Tactic := idtac.

Program Definition boz : nat := _.

Module M.

  Program Definition mboz : nat := _.
  Final Obligation.
    exact 0.
  Qed.

End M.

Final Obligation.
  exact 0.
Qed.
