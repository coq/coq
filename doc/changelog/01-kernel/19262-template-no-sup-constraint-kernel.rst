- **Changed:**
  the criteria for a parameter to be considered template in a template inductive type.
  For a level to be template, it must now appear only once in the context of parameters,
  and only as the return sort of the arity of some parameter. Furthermore,
  it may appear neither in the indices of the inductive type nor in the type of its constructors.
  Finally, a template level appearing in the return sort of the inductive type must have a zero increment
  (`#19250 <https://github.com/coq/coq/pull/19250>`_,
  `#19254 <https://github.com/coq/coq/pull/19254>`_,
  `#19263 <https://github.com/coq/coq/pull/19263>`_,
  by Pierre-Marie Pédrot).
- **Changed:**
  the kernel typing rules for template polymorphic inductive types do not
  require anymore adding global constraints when applied enough. Rather,
  template polymorphic inductive types are now a special kind of universe
  polymorphic inductive types that do not need explicit instances and
  can handle some amount of algebraic universe levels. The new rules are
  strictly more general than the previous ones and thus backwards compatible
  (`#19262 <https://github.com/coq/coq/pull/19262>`_,
  by Pierre-Marie Pédrot).
