- **Changed:**
  the implicit universe level generated when an evar must be a sort
  is now flexible instead of rigid. In particular this allows it to be unified with `Set`,
  e.g. `Check fun A => A -> (A:Set).` now succeeds
  (the evar for the type of `A` must be a sort when `A` appears to the left of the arrow, then is unified with `Set` on the right of the arrow).
  This may cause :flag:`Universe Minimization ToSet` to minimize too much in rare cases, either use an explicit `: Type` or disable the flag to recover previous behaviour
  (`#22583 <https://github.com/rocq-prover/rocq/pull/22583>`_,
  by Gaëtan Gilbert).
