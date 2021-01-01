- **Changed:**
  The term representation of pattern-matchings now uses a compact form that
  provides a few static guarantees such as eta-expansion of branches and return
  clauses and is usually more efficient. The most visible user change is that for
  the time being, the :tacn:`destruct` tactic and its variants generate dummy
  cuts (β redexes) in the branches of the generated proof.
  This can also generate very uncommon backwards incompatibilities, such as a
  change of occurrence numbering for subterms, or breakage of unification in
  complex situations involving pattern-matchings whose underlying inductive type
  declares let-bindings in parameters, arity or constructor types. For ML plugin
  developers, an in-depth description of the new representation, as well as
  porting tips, can be found in dev/doc/case-repr.md
  (`#13563 <https://github.com/coq/coq/pull/13563>`_,
  fixes `#3166 <https://github.com/coq/coq/issues/3166>`_,
  by Pierre-Marie Pédrot).
