- **Changed:**
  :cmd:`Print Assumptions` reports the impredicativity of :g:`Set` as an
  assumption of a definition or inductive type only when it actually
  relies on it (to typecheck at all, or for its elimination rules),
  rather than for anything typechecked with ``-impredicative-set``
  (`#22166 <https://github.com/rocq-prover/rocq/pull/22166>`_,
  by Jason Gross).
