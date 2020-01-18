- **Changed:**
  The default tactic used by :g:`firstorder` is
  :g:`auto with core` instead of :g:`auto with *`;
  see :ref:`decisionprocedures` for details;
  old behavior can be reset by using the `-compat 8.12` command-line flag;
  to ease the migration of legacy code, the default solver can be set to `debug auto with *`
  with `Set Firstorder Solver debug auto with *`
  (`#11760 <https://github.com/coq/coq/pull/11760>`_,
  by Vincent Laporte).
