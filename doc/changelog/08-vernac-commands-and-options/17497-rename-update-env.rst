- **Changed:**
  arguments renamed by :cmd:`Arguments` (including anonymous arguments which can be renamed without using `: rename`)
  are now applied more consistently. This may break proof scripts which rely on some tactic incorrectly using the original names
  (`#17497 <https://github.com/coq/coq/pull/17497>`_,
  by Gaëtan Gilbert).
