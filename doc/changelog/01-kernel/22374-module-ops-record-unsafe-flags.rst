- **Fixed:**
  :cmd:`Print Assumptions` and :cmd:`rocqchk`'s context summary now report the
  checks that were disabled while a module operation ran. Previously the flags
  of a body inlined for ``Parameter Inline``, and the flags in force during a
  functor application, an :cmd:`Include` or the sealing of a module by a
  signature, were both lost, so a definition obtained that way was reported as
  closed under the global context; :cmd:`rocqchk` rejected some of these files
  outright instead of reporting them
  (`#22374 <https://github.com/rocq-prover/rocq/pull/22374>`_,
  fixes `#12155 <https://github.com/rocq-prover/rocq/issues/12155>`_
  and `#16646 <https://github.com/rocq-prover/rocq/issues/16646>`_,
  by Jason Gross).
