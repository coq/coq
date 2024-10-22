- **Changed:**
  The :cmd:`Hint Rewrite` command now requires a *non-empty* list of hintDbs
  after the colon to be consistent with other Hint commands.  If your script
  has an empty list of hintDbs, fix it by removing the colon
  (`#19730 <https://github.com/coq/coq/pull/19730>`_,
  by Jim Fehrle).
