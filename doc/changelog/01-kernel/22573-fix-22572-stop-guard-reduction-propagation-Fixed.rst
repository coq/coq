- **Fixed:**
  Reject non-terminating fixpoints whose invalid recursive calls were erased after speculative guard checking of a stuck match, while preserving nested fixpoints on constructed arguments
  (`#22573 <https://github.com/rocq-prover/rocq/pull/22573>`_,
  fixes `#22572 <https://github.com/rocq-prover/rocq/issues/22572>`_,
  by Thomas Lamiaux).
