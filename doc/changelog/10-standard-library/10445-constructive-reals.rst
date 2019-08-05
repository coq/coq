- New module `Reals.ConstructiveCauchyReals` defines constructive real numbers
  by Cauchy sequences of rational numbers. Classical real numbers are now defined
  as a quotient of these constructive real numbers, which significantly reduces
  the number of axioms needed (see `Reals.Rdefinitions` and `Reals.Raxioms`),
  while preserving backward compatibility.

  Futhermore, the new axioms for classical real numbers include the limited
  principle of omniscience (`sig_forall_dec`), which is a logical principle
  instead of an ad hoc property of the real numbers.

  See `#10445 <https://github.com/coq/coq/pull/10445>`_, by Vincent Semeria,
  with the help and review of Guillaume Melquiond and Bas Spitters.
