- **Changed:**
  Ltac2 are typechecked at declaration time by default.
  This should produce better errors when a notation argument does not have the expected type
  (e.g. wrong branch type in `match! goal`).
  The previous behaviour of typechecking only the expansion result can be
  recovered using :flag:`Ltac2 Typed Notations`. We believe there are no real
  use cases for this, please report if you have any
  (`#18432 <https://github.com/coq/coq/pull/18432>`_,
  fixes `#17477 <https://github.com/coq/coq/issues/17477>`_,
  by Gaëtan Gilbert).
