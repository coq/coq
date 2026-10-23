- **Added:** :cmd:`Hint Resolve` and :cmd:`Hint Constructors` now support
  :attr:`export` and :attr:`global` inside sections.  Hints are rebuilt from
  their generalized types when the section closes, recomputing implicit costs
  while preserving explicit costs.  Explicit hint patterns, section-variable
  hints, and hints without a global head after discharge remain unsupported;
  see :ref:`creating_hints` (by Jan-Oliver Kaiser).
