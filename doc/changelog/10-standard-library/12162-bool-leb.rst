- **Deprecated:**
  ``Bool.leb`` in favor of ``Bool.le``. The definition of ``Bool.le`` is made local to avoid conflicts with ``Nat.le``. As a consequence, previous calls to ``leb`` based on importing ``Bool`` should now be qualified into ``Bool.le`` even if ``Bool`` is imported.
  (`#12162 <https://github.com/coq/coq/pull/12162>`_,
  by Olivier Laurent).
