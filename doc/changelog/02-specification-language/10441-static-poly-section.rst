- The universe polymorphism setting now applies from the opening of a section.
  In particular, it is not possible anymore to mix polymorphic and monomorphic
  definitions in a section when there are no variables nor universe constraints
  defined in this section. This makes the behaviour consistent with the
  documentation. (`#10441 <https://github.com/coq/coq/pull/10441>`_,
  by Pierre-Marie Pédrot)

- The :cmd:`Section` vernacular command now accepts the "universes" attribute. In
  addition to setting the section universe polymorphism, it also locally sets
  the universe polymorphic option inside the section.
  (`#10441 <https://github.com/coq/coq/pull/10441>`_, by Pierre-Marie Pédrot)
