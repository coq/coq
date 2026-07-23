- **Added:**
  :cmd:`Print Assumptions` and the checker (``rocqchk``) now report
  inductive types and constants whose sort elimination constraints were
  not checked (typing flag ``check_eliminations = false``), which was
  previously silently ignored, and :cmd:`Print Typing Flags` now also
  displays that flag when it has been disabled. The flag has no vernacular setter by design; it can
  only be disabled from a plugin (via ``Global.set_typing_flags``), as
  done for instance by ``rocq-lean-import``
  (`#22294 <https://github.com/rocq-prover/rocq/pull/22294>`_,
  by Jason Gross).
