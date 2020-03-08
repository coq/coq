- **Removed:**
  The undocumented ``omega with`` tactic variant has been removed,
  using :tacn:`lia` is the recommended replacement, although the old semantics
  of ``omega with *`` can also be recovered with ``zify; omega``
  (`#11288 <https://github.com/coq/coq/pull/11288>`_,
  by Emilio Jesus Gallego Arias).
