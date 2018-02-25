- **Changed:**
  When applied on proofs, the tactics "elim" and "induction" now use
  dependent elimination by default whenever needed, as it is the case
  with expressions whose type is not in Prop. The former behavior can
  be restored by issuing "Unset Dependent Propositions Induction"
  (`#6833 <https://github.com/coq/coq/pull/6833>`_,
  by Hugo Herbelin).
