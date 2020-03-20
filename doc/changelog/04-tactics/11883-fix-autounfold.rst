- **Fixed:**
  The behavior of :tacn:`autounfold` no longer depends on the names of terms and modules
  (`#11883 <https://github.com/coq/coq/pull/11883>`_,
  fixes `#7812 <https://github.com/coq/coq/issues/7812>`_,
  by Attila Gáspár).
- **Changed:**
  `at` clauses can no longer be used with :tacn:`autounfold`. Since they had no effect, it is safe to remove them
  (`#11883 <https://github.com/coq/coq/pull/11883>`_,
  by Attila Gáspár).
- **Changed:**
  :tacn:`autounfold` no longer fails when the :cmd:`Opaque` command is used on constants in the hint databases
  (`#11883 <https://github.com/coq/coq/pull/11883>`_,
  by Attila Gáspár).
