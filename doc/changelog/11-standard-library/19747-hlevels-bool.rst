- **Changed:** split :g:`HLevels` into :g:`HLevelsBase`, which does not depend
  on axioms, and :g:`HLevels`, which includes the former and provides the
  previous functionality.
  **Added:** transparent lemmas :g:`false_hprop`, :g:`true_hprop`,
  :g:`Is_true_hprop`, and a wrappers :g:`transparent_Is_true` and
  :g:`transparent_eq_true` to produce transparent proofs for :g:`Is_true` and
  :g:`eq_true` given not necessarily transparent proofs
  (`#19747 <https://github.com/coq/coq/pull/19747>`_,
  by Andres Erbsen).
