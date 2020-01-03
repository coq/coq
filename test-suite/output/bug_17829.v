Tactic Notation (at level 3) "foo" tactic2(tac) := intro; tac.
Ltac f := foo (foo idtac).
Print Ltac f.
