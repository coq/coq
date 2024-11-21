- **Changed:**
  `coq_makefile` generated makefiles only install plugin `.cmxs` files in findlib locations
  and stop putting a copy in `user-contrib` (the copy should be useless after the removal of plugin legacy loading)
  (`#19841 <https://github.com/coq/coq/pull/19841>`_,
  by Gaëtan Gilbert).
