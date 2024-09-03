- **Changed:**
  `Ncring_tac.extra_reify` is expected to return `tt` on failure and
  the reification result on success, instead of `(false, anything)` on failure
  and `(true, result)` on success
  (this only matters to users overriding it to extend the Ncring reification)
  (`#19501 <https://github.com/coq/coq/pull/19501>`_,
  by Gaëtan Gilbert).
