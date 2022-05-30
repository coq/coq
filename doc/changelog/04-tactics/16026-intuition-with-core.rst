- **Deprecated:** the default ``intuition_solver`` (see
  :tacn:`intuition`) now outputs warning ``intuition-auto-with-star``
  if it solves a goal with ``auto with *`` that was not solved with
  just :tacn:`auto`. In a future version it will be changed to just
  :tacn:`auto`. Use ``intuition tac`` locally or ``Ltac
  Tauto.intuition_solver ::= tac`` globally to silence the warning in
  a forward compatible way with your choice of tactic ``tac``
  (``auto``, ``auto with *``, ``auto with`` your prefered databases,
  or any other tactic) (`#16026
  <https://github.com/coq/coq/pull/16026>`_, by Gaëtan Gilbert).
