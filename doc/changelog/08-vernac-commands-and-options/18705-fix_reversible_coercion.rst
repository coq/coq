- **Changed:**
  the default reversibility status of most coercions.
  The refman states that

     By default coercions are not reversible
     except for Record fields specified using ``:>``.

  The previous code was making way too many coercion reversible by default.
  The new behavior should be closer from the spec in the doc
  (`#18705 <https://github.com/coq/coq/pull/18705>`_,
  by Pierre Roux).
