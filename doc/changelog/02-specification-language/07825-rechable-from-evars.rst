- **Changed:**
  In :tacn:`refine`, new existential variables unified with existing ones are no
  longer considered as fresh. The behavior of :tacn:`simple refine` no longer depends on
  the orientation of evar-evar unification problems, and new existential variables
  are always turned into (unshelved) goals. This can break compatibility in
  some cases (`#7825 <https://github.com/coq/coq/pull/7825>`_, by Matthieu
  Sozeau, with help from Maxime Dénès, review by Pierre-Marie Pédrot and
  Enrico Tassi, fixes `#4095 <https://github.com/coq/coq/issues/4095>`_ and
  `#4413 <https://github.com/coq/coq/issues/4413>`_).
