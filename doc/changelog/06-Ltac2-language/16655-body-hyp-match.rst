- **Added:**
  :tacn:`match! goal` support for matching hypothesis bodies
  (`#16655 <https://github.com/coq/coq/pull/16655>`_,
  fixes `#12803 <https://github.com/coq/coq/issues/12803>`_,
  by Gaëtan Gilbert).
- **Changed:**
  goal matching functions from ``Ltac2.Pattern`` (``matches_goal``, ``lazy_goal_match0``, ``multi_goal_match0`` and ``one_goal_match0``) have changed types to support matching hypothesis bodies
  (`#16655 <https://github.com/coq/coq/pull/16655>`_,
  by Gaëtan Gilbert).
