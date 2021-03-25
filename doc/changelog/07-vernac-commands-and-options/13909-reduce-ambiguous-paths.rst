- **Changed:**
  Improve the :cmd:`Coercion` command to reduce the number of ambiguous paths to
  report. A pair of multiple inheritance paths that can be reduced to smaller
  adjoining pairs will not be reported as ambiguous paths anymore.
  (`#13909 <https://github.com/coq/coq/pull/13909>`_,
  by Kazuhiko Sakaguchi).
