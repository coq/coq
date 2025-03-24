- **Changed:**
  :cmd:`Ltac` redefinitions (`Ltac foo ::= ...`) are not undone by
  importing the module containing the original definition.
  To get the previous behaviour, add `Ltac foo ::= orig_def.`
  after the original definition `Ltac foo := orig_def.`
  (`#20391 <https://github.com/coq/coq/pull/20391>`_,
  by Gaëtan Gilbert).
