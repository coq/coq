- **Fixed:**
  Guard checking forgot to check non principal arguments of a fixpoint
  for unguarded uses of the fixpoint leading to an inconsistency
  (`#20415 <https://github.com/coq/coq/pull/20415>`_,
  fixes `#20413 <https://github.com/coq/coq/issues/20413>`_,
  by Gaëtan Gilbert).
