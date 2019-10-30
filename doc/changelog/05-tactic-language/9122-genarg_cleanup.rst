- **Changed:**
  Some duplicated grammar binders in tactic notations have been
  removed, for example in ``Tactic Notation "foo" ref(x) := idtac.``
  you now must use ``reference(x)``, etc.... The full list is:
  + `integer` -> `int`
  + `clause_dft_concl` -> `clause`
  + `global` / `ref` -> `reference`
  + `quant_hyp` -> `quantified_hypothesis`
  (`#9122 <https://github.com/coq/coq/pull/9122>`_,
  by Emilio Jesus Gallego Arias).
