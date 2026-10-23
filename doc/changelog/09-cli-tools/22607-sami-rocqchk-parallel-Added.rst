- **Added:**
  ``rocqchk -j n`` checks opaque proofs in parallel, in up to *n* worker
  processes created with ``fork``, and ``-worker-budget s`` bounds how long
  a worker lives before it gives its unchecked proofs back
  (see :ref:`rocqchk`)
  (`#22607 <https://github.com/rocq-prover/rocq/pull/22607>`_,
  by Jason Gross and Sami Jawhar, based on the deferred checking of
  opaque proofs of `#22520 <https://github.com/rocq-prover/rocq/pull/22520>`_
  by Gaëtan Gilbert).
