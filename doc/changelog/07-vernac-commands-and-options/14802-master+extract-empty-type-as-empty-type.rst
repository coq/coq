- **Changed:**
  In extraction to OCaml, empty types in :n:`Type` (such as
  :n:`Empty_set`) are now extracted to an abstract type (empty by
  construction) rather than to the OCaml's :n:`unit` type
  (`#14802 <https://github.com/coq/coq/pull/14802>`_,
  fixes a remark at `#14801 <https://github.com/coq/coq/issues/14801>`_,
  by Hugo Herbelin).
