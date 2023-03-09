- **Fixed:**
  Pattern-matching clauses were possibly lost when matching over a
  constructor from a singleton inductive type in the presence of
  implicit coercions (`#17138 <https://github.com/coq/coq/pull/17138>`_,
  fixes `#17137 <https://github.com/coq/coq/issues/17137>`_, by Hugo
  Herbelin).
