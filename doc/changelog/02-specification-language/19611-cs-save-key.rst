- **Changed:**
  The unification algorithm does not solve unification problems of the
  form `proj _ ~ _` using canonical structures when the LHS reduces or
  is ground
  (`#19611 <https://github.com/coq/coq/pull/19611>`_,
  by ).
