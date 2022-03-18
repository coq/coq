- **Fixed:**
  When :tacn:`setoid_rewrite` succeeds in rewriting at some occurrence but the resulting equality is the identity, it now tries rewriting in subterms of that occurrence instead of giving up
  (`#15612 <https://github.com/coq/coq/pull/15612>`_,
  fixes `#8080 <https://github.com/coq/coq/issues/8080>`_,
  by Gaëtan Gilbert).
