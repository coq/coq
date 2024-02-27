- **Fixed:**
  Wrongly self-referencing extraction of primitive projections to OCaml in functors
  (`#17321 <https://github.com/coq/coq/pull/17321>`_,
  fixes `#16288 <https://github.com/coq/coq/issues/16288>`_,
  by Hugo Herbelin). Note that OCaml wrappers assuming that the
  applicative syntax of projections is provided may have
  to use the dot notation instead.
