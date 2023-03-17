- **Changed:**
  in the fringe case where the ``with`` clause of a call to :tacn:`specialize`
  depends on a variable bound in the type, the tactic will now fail instead of
  silently producing a shelved evar
  (`#17322 <https://github.com/coq/coq/pull/17322>`_,
  by Pierre-Marie Pédrot).
