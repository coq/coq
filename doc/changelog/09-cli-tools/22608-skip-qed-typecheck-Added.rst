- **Added:**
  ``-skip-qed-typecheck`` option of ``rocq compile``, which skips the kernel
  typechecking of opaque proofs at :cmd:`Qed`; :cmd:`Print Assumptions` reports
  each such proof and ``rocqchk`` still checks it
  (`#22608 <https://github.com/rocq-prover/rocq/pull/22608>`_,
  by Sami Jawhar).
