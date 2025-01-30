- **Changed:**
  :cmd:`Ltac` redefinitions (`Ltac ::=`) understand :attr:`export`.
  Previously :attr:`global` and the default locality meant the redefinition would
  take effect at Require time and when importing any surrounding module.
  Now :attr:`global` means it takes affect at Require time,
  :attr:`export` when the current module (but not its parents) is imported,
  and the default is equivalent to the combination of :attr:`global` and :attr:`export`
  (`#20054 <https://github.com/coq/coq/pull/20054>`_,
  by Gaëtan Gilbert).
