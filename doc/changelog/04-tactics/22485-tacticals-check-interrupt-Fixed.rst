- **Fixed:**
  :tacn:`do` now checks for an interrupt between iterations, as
  :tacn:`repeat` already did, so an IDE can stop a long :tacn:`do` loop.
  :tacn:`autorewrite`, :tacn:`rewrite` with a ``?`` or ``!`` multiplier and
  Ltac2's ``do`` had the same gap
  (`#22485 <https://github.com/rocq-prover/rocq/pull/22485>`_,
  by remix7531).
