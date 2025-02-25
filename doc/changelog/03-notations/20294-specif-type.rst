- **Changed:**
  The `Specif` notations (`exists x : A, P`, `{ x : A | P }`, `{ x : A & P }`, etc)
  locally open `type_scope` for the second component (`P`).
  This makes eg `{ x & type_1 * type_2 }` work even when `nat_scope` is opened instead of interpreting `*` as peano multiplication
  (`#20294 <https://github.com/coq/coq/pull/20294>`_,
  by Gaëtan Gilbert).
