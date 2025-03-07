- **Changed:**
  :opt:`Printing Depth` completely skips subterms beyond the given depth.
  In general the formatter depth is higher than the term depth, so there is no visible change,
  but some notations print subterms without increasing the formatting depth in which case
  you may need to increase the printing depth to avoid `...`
  (`#20275 <https://github.com/coq/coq/pull/20275>`_,
  by Gaëtan Gilbert).
