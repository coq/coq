- **Added:**
  Ltac2 record expressions support punning, i.e. ``{ foo; M.bar }`` is equivalent to ``{ foo := foo; M.bar := bar }``
  (`#16556 <https://github.com/coq/coq/pull/16556>`_,
  by Gaëtan Gilbert).
