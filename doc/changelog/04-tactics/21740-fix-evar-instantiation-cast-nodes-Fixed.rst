- **Added:**
  flags :flag:`Unification Recheck Casts` and :flag:`Unification Full Retyping`
  to control universe constraint checking during evar instantiation.
  :flag:`Unification Recheck Casts` (off by default) makes the evar solver
  validate Cast nodes after inverting substitutions.
  :flag:`Unification Full Retyping` (off by default) makes the evar solver
  use full type checking instead of fast retyping when validating evar bodies.
  Either flag independently fixes the bug
  (`#21740 <https://github.com/rocq-prover/rocq/pull/21740>`_,
  fixes `#21733 <https://github.com/rocq-prover/rocq/issues/21733>`_,
  by Jason Gross).
