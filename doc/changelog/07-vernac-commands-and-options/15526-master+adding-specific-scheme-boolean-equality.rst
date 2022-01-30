- **Added:**
  :cmd:`Scheme Boolean Equality` command to generate the boolean
  equality for an inductive type whose equality is
  decidable.  It is useful when Coq is able to generate the boolean
  equality but isn't powerful enough to prove the decidability of
  equality (unlike :cmd:`Scheme Equality`, which tries to
  prove the decidability of the type)
  (`#15526 <https://github.com/coq/coq/pull/15526>`_,
  by Hugo Herbelin).
