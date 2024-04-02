Require Import Coq.Program.Tactics.

Local Obligation Tactic := abstract exact I.

Program Definition foo : True := _.

Definition bar : True := ltac:(abstract exact I).
