- Fix two bugs in `Export`. This can have an impact on the behavior of the
  `Import` command on libraries. `Import A` when `A` imports `B` which exports
  `C` was importing `C`, whereas `Import` is not transitive. Also, after
  `Import A B`, the import of `B` was sometimes incomplete.
  (`#10476 <https://github.com/coq/coq/pull/10476>`_, by Maxime Dénès).
