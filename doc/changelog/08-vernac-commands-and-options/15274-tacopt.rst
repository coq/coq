- **Changed:** commands which set tactic options (currently
  :opt:`Firstorder Solver` and :cmd:`Obligation Tactic`, as well as any
  defined by third party plugins) now support :attr:`export` locality.
  Note that such commands using :attr:`global` without :attr:`export`
  or using no explicit locality outside sections apply their effects
  when any module containing it (recursively) is imported. This will
  change in a future version. (`#15274
  <https://github.com/coq/coq/pull/15274>`_, fixes `#15072
  <https://github.com/coq/coq/issues/15072>`_, by Gaëtan Gilbert).
