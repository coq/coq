- **Added:**
  :opt:`Debug` to control debug messages, functioning similarly to the warning system
  (`#13202 <https://github.com/coq/coq/pull/13202>`_,
  by Maxime Dénès and Gaëtan Gilbert).
  The following flags have been converted (such that ``Set Flag`` becomes ``Set Debug "flag"``):

  - ``Debug Unification`` to ``unification``

  - ``Debug HO Unification`` to ``ho-unification``

  - ``Debug Tactic Unification`` to ``tactic-unification``

  - ``Congruence Verbose`` to ``congruence``

  - ``Debug Cbv`` to ``cbv``

  - ``Debug RAKAM`` to ``RAKAM``

  - ``Debug Ssreflect`` to ``ssreflect``
