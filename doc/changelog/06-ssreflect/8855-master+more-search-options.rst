- **Changed:** The :cmd:`Search (ssreflect)` command that used to be
  available when loading the `ssreflect` plugin has been moved to a
  separate plugin that needs to be loaded separately: `ssrsearch`
  (part of `#8855 <https://github.com/coq/coq/pull/8855>`_, fixes
  `#12253 <https://github.com/coq/coq/issues/12253>`_, by Théo
  Zimmermann).

- **Deprecated:** :cmd:`Search (ssreflect)` (available through
  `Require ssrsearch.`) in favor of the `headconcl:` clause of
  :cmd:`Search` (part of `#8855
  <https://github.com/coq/coq/pull/8855>`_, by Théo Zimmermann).
