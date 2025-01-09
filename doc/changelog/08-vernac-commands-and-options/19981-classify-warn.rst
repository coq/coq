- **Fixed:**
  :opt:`Debug` and :opt:`Warnings` are classified as Synterp.
  This changes the scheduling during :cmd:`Import` such that putting `#[export] Set Warnings` around a specific command may change behaviour.
  (`#19981 <https://github.com/coq/coq/pull/19981>`_,
  by Gaëtan Gilbert).
