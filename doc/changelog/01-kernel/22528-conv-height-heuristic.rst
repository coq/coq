- **Added:**
  New flag :flag:`Kernel Conversion Height Heuristic` that enables a conversion
  heuristic when comparing two constants.
  The kernel now calculates the definitional height of constants upon definition,
  which corresponds to the maximum number of constants that need to be unfolded
  to arrive at a term with no constants left to unfold.
  The definitional height is stored in a new field of the `constant_body` record.
  When enabled, the heuristic uses these heights to over-approximate dependencies
  between constants. Namely, if :g:`c1` depends on :g:`c2`, then
  :g:`||c1|| > ||c2||`. During conversion, if the oracle gives the same priority
  to two constants, the heuristic will prefer unfolding the one with the greatest
  definitional height.
  (`#22528 <https://github.com/rocq-prover/rocq/pull/22528>`_,
  by Gaspar Ricci).
