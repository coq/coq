- **Changed:** commands setting tactic options (currently
  :opt:`Firstorder Solver` and :cmd:`Obligation Tactic`, as well as any
  defined by third party plugins) now support :attr:`export` locality.
  Note that the meaning of :attr:`global` and the default outside
  sections currently also set the option when importing any
  surrounding module. This will change in a future version. (`#15274
  <https://github.com/coq/coq/pull/15274>`_, fixes `#15072
  <https://github.com/coq/coq/issues/15072>`_, by Gaëtan Gilbert).
