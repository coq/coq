- **Fixed:**
  The :tacn:`clear dependent <clear>` tactic now does not backtrack
  internally, preventing an exponential blowup
  (`#14984 <https://github.com/coq/coq/pull/14984>`_,
  fixes `#11689 <https://github.com/coq/coq/issues/11689>`_,
  by Pierre-Marie Pédrot).
