- **Added:**
  :tacn:`intuition` and :tacn:`dintuition` use ``Tauto.intuition_solver`` (defined as ``auto with *``) instead of hardcoding ``auto with *``.
  This makes it possible to change the default solver with ``Ltac Tauto.intuition_solver ::= ...``
  (`#15866 <https://github.com/coq/coq/pull/15866>`_,
  fixes `#7725 <https://github.com/coq/coq/issues/7725>`_,
  by Gaëtan Gilbert).
