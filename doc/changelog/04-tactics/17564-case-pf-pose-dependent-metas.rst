- **Fixed:**
  intropatterns destructing a term whose type is a product
  cannot silently create shelved evars anymore. Instead, it
  fails with an unsolvable variable. This can be fixed in a
  backwards compatible way by using the e-variant of the parent
  tactic
  (`#17564 <https://github.com/coq/coq/pull/17564>`_,
  by Pierre-Marie Pédrot).
- **Changed:**
  the unification heuristics for implicit arguments of the :tacn:`case` tactic.
  We unconditionally recommend using :tacn:`destruct` instead, and even more so
  in case of incompatibility.
