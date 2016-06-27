Tactic Notation "complete" tactic(tac) := tac; fail.

Ltac f0 := complete (intuition idtac).
(** FIXME: This is badly printed because of bug #3079.
    At least we check that it does not fail anomalously. *)
Print Ltac f0.

Ltac f1 := complete f1.
Print Ltac f1.

Ltac f2 := complete intuition.
Print Ltac f2.
