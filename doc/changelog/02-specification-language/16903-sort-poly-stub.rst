- **Changed:**
  enhance the universe unification algorithm, which is now
  able to delay the definition of a sort. This allows omitting
  some explicit `Prop` and `SProp` annotations when writing terms.
  Some minor backwards compatibility issues can arise in rare cases,
  which can be solved with more explicit sort annotations
  (`#16903 <https://github.com/coq/coq/pull/16903>`_,
  by Pierre-Marie Pédrot).
