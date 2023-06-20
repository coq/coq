- **Changed:**
  :opt:`Warnings` and :attr:`warnings` now emit a warning when trying
  to enable an unknown warning (there is still no warning when
  disabling an unknown warning as this behavior is useful for
  compatibility, or when enabling an unknown warning through the
  command line `-w` as the warning may be in a yet to be loaded
  plugin) (`#17747 <https://github.com/coq/coq/pull/17747>`_, by
  Gaëtan Gilbert).
