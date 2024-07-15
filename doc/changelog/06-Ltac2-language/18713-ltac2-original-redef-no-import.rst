- **Changed:**
  :cmd:`Import`\ing a module containing a mutable Ltac2 definition
  does not undo its mutations. Replace `Ltac2 mutable foo := some_expr.`
  with `Ltac2 mutable foo := some_expr. Ltac2 Set foo := some_expr.`
  to recover the previous behaviour
  (`#18713 <https://github.com/coq/coq/pull/18713>`_,
  by Gaëtan Gilbert).
