- **Changed:**
  the kernel typing rules for template polymorphic inductive types do not
  require anymore adding global constraints when applied enough. Rather,
  template polymorphic inductive types are now a special kind of universe
  polymorphic inductive types that do not need explicit instances and
  can handle some amount of algebraic universe levels. The new rules are
  strictly more general than the previous ones and thus backwards compatible
  (`#19262 <https://github.com/coq/coq/pull/19262>`_,
  by Pierre-Marie Pédrot).
