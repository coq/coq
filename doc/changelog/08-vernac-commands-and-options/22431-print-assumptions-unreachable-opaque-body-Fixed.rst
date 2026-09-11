- **Fixed:**
  :cmd:`Print Assumptions` reported an opaque constant whose body it could
  not read as an axiom, which is what happens to every proof coming from a
  library compiled with ``-vos``, and in particular in ``-vok`` builds (see
  :ref:`compiled-interfaces`). Such a constant is now listed under its own
  ``Opaque proofs that could not be accessed:`` heading instead of under
  ``Axioms:``, and the new :warn:`unreachable-opaque-body` warning is
  emitted, so that the situation can be detected without reading the output
  (`#22431 <https://github.com/rocq-prover/rocq/pull/22431>`_,
  fixes `#22430 <https://github.com/rocq-prover/rocq/issues/22430>`_,
  by remix7531).
