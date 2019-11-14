- The :cmd:`Time` command and :tacn:`time` tactic now correctly report
  user and system time spent in child processes.  This means, for
  example, that these commands now play nicely with the `par:` goal
  selector and also include time spent in the OCaml compiler when
  running :tacn:`native_compute`.  (`#11125
  <https://github.com/coq/coq/pull/11125>`_ fixes `#6432
  <https://github.com/coq/coq/issues/6432>`_, by Jason Gross).
