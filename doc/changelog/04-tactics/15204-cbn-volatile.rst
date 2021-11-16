- **Changed:** :tacn:`cbn` interprets the combination of the ``!`` and
  ``/`` modifiers (from :cmd:`Arguments`) to mean "unfold as soon as
  all arguments before the ``/`` are provided and all arguments marked
  with ``!`` reduce to a constructor". This makes it unfold more often
  than without the ``/`` when all arguments are provided. Previously
  adding ``/`` would only prevent unfolding when insufficient
  arguments are provided without adding new unfoldings.

  Note that this change only takes effect in default mode (as opposed
  to when ``simpl nomatch`` was used) (`#15204
  <https://github.com/coq/coq/pull/15204>`_, fixes `#4555
  <https://github.com/coq/coq/issues/4555>`_ and `#7674
  <https://github.com/coq/coq/issues/7674>`_, by Gaëtan Gilbert).
