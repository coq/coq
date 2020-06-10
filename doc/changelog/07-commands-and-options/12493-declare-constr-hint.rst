- **Changed:**
  Declaring a hint which is not a global reference now generates
  a constant on the fly. This behaviour can be tweaked by
  unsetting the deprecated :flag:`Declare Hint Proxy` flag
  (`#12493 <https://github.com/coq/coq/pull/12493>`_,
  fixes `#11970 <https://github.com/coq/coq/issues/11970>`_,
  by Pierre-Marie Pédrot).
