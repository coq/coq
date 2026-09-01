- **Changed:**
  :cmd:`Hint Mode` containing mode ``=`` now prevent :cmd:`Hint Extern` from
  instantiating the corresponding existential variables. Code that relied on
  :cmd:`Hint Extern` instantiating an argument marked with ``=`` will no longer
  work.
  (`#22415 <https://github.com/rocq-prover/rocq/pull/22415>`_,
  by Jan-Oliver Kaiser).
