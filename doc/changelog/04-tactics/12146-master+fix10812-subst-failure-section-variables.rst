- **Changed:**
  Tactic :tacn:`subst` :n:`@ident` now fails over a section variable which is
  indirectly dependent in the goal; the incompatibility can generally
  be fixed by first clearing the hypotheses causing an indirect
  dependency, as reported by the error message, or by using :tacn:`rewrite` :n:`in *`
  instead; similarly, :tacn:`subst` has no more effect on such variables
  (`#12146 <https://github.com/coq/coq/pull/12146>`_,
  by Hugo Herbelin; fixes `#10812 <https://github.com/coq/coq/pull/10812>`_;
  fixes `#12139 <https://github.com/coq/coq/pull/12139>`_).
