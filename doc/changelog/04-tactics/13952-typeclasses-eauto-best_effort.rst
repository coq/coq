- **Added:**
  :ref:`best_effort <TypeclassesEautoBestEffort>` option to :tacn:`typeclasses eauto`,
  to return a *partial* solution to its initial proof-search problem. The goals that
  can remain unsolved are determined according to the modes declared for their head
  (see :cmd:`Hint Mode`). This is used by typeclass resolution during type
  inference to provide more informative error messages.
  (`#13952 <https://github.com/coq/coq/pull/13952>`_,
  fixes `#13942 <https://github.com/coq/coq/pull/13952>`_ and
  `#14125 <https://github.com/coq/coq/pull/14125>`_, by Matthieu Sozeau).
