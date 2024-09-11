- **Changed:**
  ``:>`` in :token:`of_type_inst` now always declares coercions. The previous behavior,
  deprecated since 8.18, was to declare typeclass instances instead,
  when used in records declared with the :cmd:`Class` keyword. Look at
  the :ref:`previous changelog entries <819_changes_spec_language>`
  about former warnings `future-coercion-class-constructor` and
  `future-coercion-class-field` for advice on how to update your code
  (`#19519 <https://github.com/coq/coq/pull/19519>`_, by Pierre Roux).
