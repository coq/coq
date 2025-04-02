- **Changed:**
  the :tacn:`abstract` tactic now only registers a name
  for the sublemma after the whole tactic block has run,
  i.e. after a dot. In particular, the sublemma cannot
  be accessed by its name while the tactic call has not
  returned
  (`#14937 <https://github.com/coq/coq/pull/14937>`_,
  by Pierre-Marie Pédrot).
