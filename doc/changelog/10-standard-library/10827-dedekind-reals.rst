- New module `Reals.ClassicalDedekindReals` defines Dedekind real numbers
  as boolean-values functions along with 3 logical axioms: limited principle
  of omniscience, excluded middle of negations and functional extensionality.
  The exposed type :g:`R` in module :g:`Reals.Rdefinitions` is those
  Dedekind reals, hidden behind an opaque module.
  Classical Dedekind reals are a quotient of constructive reals, which allows
  to transport many constructive proofs to the classical case.

  See `#10827 <https://github.com/coq/coq/pull/10827>`_, by Vincent Semeria,
  based on discussions with Guillaume Melquiond, Bas Spitters and Hugo Herbelin,
  code review by Hugo Herbelin.
