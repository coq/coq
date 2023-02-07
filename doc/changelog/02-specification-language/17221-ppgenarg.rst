- **Added:**
  when printing uninterpreted terms (for instance through :cmd:`Print Ltac` on `Ltac foo := exact some_term`),
  extensions to the term language (for instance :ref:`tactics-in-terms`) are now printed correctly instead of as holes (`_`)
  (`#17221 <https://github.com/coq/coq/pull/17221>`_,
  by Gaëtan Gilbert).
