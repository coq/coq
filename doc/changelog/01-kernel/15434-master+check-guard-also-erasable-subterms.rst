- **Changed:**
  Fixpoints are now expected to be guarded even in subterms erasable
  by reduction, thus getting rid from an artificial obstacle
  preventing to lift the assumption of weak normalization of Coq to an
  assumption of strong normalization; for instance (barring
  implementation bugs) termination of the type-checking algorithm of
  Coq is now restored (of course, as usual, up to the assumption of
  the consistency of set theory and type theory, i.e., equivalently,
  up to the weak normalization of type theory, a "physical"
  assumption, which has not been contradicted for decades and which
  specialists commonly believe to be a truth)
  (`#15434 <https://github.com/coq/coq/pull/15434>`_, incidentally
  fixes the complexity issue `#5702
  <https://github.com/coq/coq/issues/5702>`_, by Hugo Herbelin).
