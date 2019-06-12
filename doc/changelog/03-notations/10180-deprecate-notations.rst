- The :cmd:`Notation` and :cmd:`Infix` commands now support the `deprecated`
  attribute. The former `compat` annotation for notations is
  deprecated, and its semantics changed. It is now made equivalent to using
  a `deprecated` attribute, and is no longer connected with the `-compat`
  command-line flag.
  (`#10180 <https://github.com/coq/coq/pull/10180>`_, by Maxime Dénès).
