- **Changed:**
  :cmd:`Guarded` and :cmd:`Validate Proof` are now internally classified as "queries" instead of "proof steps".
  This means they should not be counted anymore when stepping back with :cmd:`Undo`.
  (`#19383 <https://github.com/coq/coq/pull/19383>`_,
  by Gaëtan Gilbert).
