- **Changed:**
  :cmd:`Print Assumptions` and the :cmd:`Print Opaque Dependencies`,
  :cmd:`Print Transparent Dependencies` and :cmd:`Print All Dependencies`
  commands reuse the traversal of objects that an earlier query in the same
  global environment already walked, instead of walking them again; the
  ``assumptions-cache`` component of :opt:`Debug` reports each reuse
  (`#22610 <https://github.com/rocq-prover/rocq/pull/22610>`_,
  fixes `#5639 <https://github.com/rocq-prover/rocq/issues/5639>`_,
  by Sami Jawhar).
