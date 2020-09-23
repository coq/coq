- **Fixed:**
  Targets such as ``print-pretty-timed`` in ``coq_makefile``-made
  ``Makefile``\s no longer error in rare cases where ``--output-sync`` is not
  passed to make and the timing output gets interleaved in just the wrong way
  (`#13063 <https://github.com/coq/coq/pull/13063>`_, fixes `#13062
  <https://github.com/coq/coq/issues/13062>`_, by Jason Gross).
