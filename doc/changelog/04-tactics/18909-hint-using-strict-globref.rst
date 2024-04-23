- **Changed:**
  syntactic global references passed through the `using` clauses of :tacn:`auto`-like
  tactics are now handled as plain references rather than interpreted terms. In
  particular, their typeclass arguments will not be inferred. In general, the previous
  behaviour can be emulated by replacing `auto using foo` with `pose proof foo; auto`
  (`#18909 <https://github.com/coq/coq/pull/18909>`_,
  by Pierre-Marie Pédrot).
