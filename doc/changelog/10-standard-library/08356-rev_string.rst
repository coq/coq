- Added ``String.rev`` and proved some lemmas about it
  (`#8356 <https://github.com/coq/coq/pull/8356>`_, by Yishuai Li).
  Note that this might cause incompatibilities if you have, e.g.,
  ``List`` and ``String`` both imported with ``String`` on top,
  and expect ``rev`` to refer to ``List.rev``.
  Solution: qualify ``rev``.
