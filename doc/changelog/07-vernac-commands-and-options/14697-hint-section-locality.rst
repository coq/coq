- **Added:**
  The :cmd:`Hint Cut`, :cmd:`Hint Mode`, :cmd:`Hint Transparent` and
  :cmd:`Hint Opaque` commands now accept the :attr:`export` and :attr:`global`
  locality attributes inside sections. With either attribute, the commands will
  trigger the `non-local-section-hint` warning if the arguments refer to local
  section variables
  (`#14697 <https://github.com/coq/coq/pull/14697>`_,
  by Pierre-Marie Pédrot).
