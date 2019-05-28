- Function always opens a proof when used with a ``measure`` or ``wf``
  annotation, see :ref:`advanced-recursive-functions` for the updated
  documentation (`#10215 <https://github.com/coq/coq/pull/10215>`_,
  by Enrico Tassi).

- The legacy command Add Morphism always opens a proof and cannot be used
  inside a module type. In order to declare a module type parameter that
  happens to be a morphism, use ``Parameter Morphism``. See
  :ref:`deprecated_syntax_for_generalized_rewriting` for the updated
  documentation (`#10215 <https://github.com/coq/coq/pull/10215>`_,
  by Enrico Tassi).
