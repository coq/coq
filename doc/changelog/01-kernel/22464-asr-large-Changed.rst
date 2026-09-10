- **Changed:**
  ``PrimInt63.asr x y`` is now ``-1`` when ``x < 0`` and ``y >= 63``,
  as prescribed by its specification ``Sint63Axioms.asr_spec``
  (`#22464 <https://github.com/rocq-prover/rocq/pull/22464>`_,
  fixes `#22462 <https://github.com/rocq-prover/rocq/issues/22462>`_,
  by Pierre Roux).
