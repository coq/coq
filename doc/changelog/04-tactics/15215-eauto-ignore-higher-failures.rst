- **Changed:**
  The :tacn:`eauto` tactic does not propagate internal Ltac failures
  with level > 0 anymore. Any failure caused by a hint now behaves as if it
  were a level 0 error
  (`#15215 <https://github.com/coq/coq/pull/15215>`_,
  fixes `#15214 <https://github.com/coq/coq/issues/15214>`_,
  by Pierre-Marie Pédrot).
