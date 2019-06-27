- New module `Reals.ConstructiveCauchyReals` defines constructive real numbers
  by Cauchy sequences of rational numbers. Classical real numbers are now defined
  as a quotient of these constructive real numbers, which significantly reduces
  the number of axioms needed (see `Reals.Rdefinitions` and `Reals.Raxioms`),
  while preserving backward compatibility.

  Futhermore, the new axioms for classical real numbers include the limited
  principle of omniscience (`sig_forall_dec`), which is a logical principle
  instead of an ad hoc property of the real numbers. In a future pull request
  we propose to deduce the other axiom, `completeness`, from the logical
  principle `sig_not_dec` (see `Reals.Rlogic`), which is the excluded middle
  of negations in sort `Type`.

  If we want the axioms to be completely logical, we could also replace the
  quotient axioms by functional extensionality, which gives the correct
  equality to the equivalences classes represented as `bool`-valued functions
  (also using Hedberg to get the unicity of proofs that those functions
  are indeed equivalence classes). However that last part is not
  completely backward compatible : it assumes funext, which is more
  powerful than ad hoc quotient axioms.

  Future work includes the development of constructive analysis, by
  moving the constructive lemmas in new modules (see `Reals.RIneq_constr`),
  and by interfacing tighter with libraries C-CoRN and math-classes.
  Since the constructive definitions are weaker, this will require
  to adapt the definitions in some places. We also need to work on
  efficient extractions of constructive real numbers, so that we can
  compute them in practice.

  See `#10445 <https://github.com/coq/coq/pull/10445>`_, by Vincent Semeria.
