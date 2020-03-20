- **Added:**
  New attributes supported when defining an inductive type
  :attr:`universes(cumulative)`, :attr:`universes(noncumulative)` and
  :attr:`private(matching)`, which correspond to legacy attributes
  ``Cumulative``, ``NonCumulative``, and the so far undocumented
  ``Private`` (`#11665 <https://github.com/coq/coq/pull/11665>`_, by
  Théo Zimmermann).

- **Changed:**
  Legacy attributes can now be passed in any order.  See
  :ref:`gallina-attributes` (`#11665
  <https://github.com/coq/coq/pull/11665>`_, by Théo Zimmermann).
