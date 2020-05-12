- **Added:** Support for new clauses `hyp:`, `headhyp:`, `concl:`,
  `headconcl:`, `head:` and `is:` in :cmd:`Search`.  Support for
  complex search queries combining disjunctions, conjunctions and
  negations (`#8855 <https://github.com/coq/coq/pull/8855>`_, by Hugo
  Herbelin, with ideas from Cyril Cohen and help from Théo
  Zimmermann).
- **Deprecated:** :cmd:`SearchHead` in favor of the new `headconcl:`
  clause of :cmd:`Search` (part of `#8855
  <https://github.com/coq/coq/pull/8855>`_, by Théo Zimmermann).
