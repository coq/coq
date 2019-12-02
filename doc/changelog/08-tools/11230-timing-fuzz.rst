- **Added:**
  The ``make-both-single-timing-files.py`` script now accepts a
  ``--fuzz=N`` parameter on the command line which determines how many
  characters two lines may be offset in the "before" and "after" timing
  logs while still being considered the same line.  When invoking this
  script via the ``print-pretty-single-time-diff`` target in a
  ``Makefile`` made by ``coq_makefile``, you can set this argument by
  passing ``TIMING_FUZZ=N`` to ``make``.  (`#11230
  <https://github.com/coq/coq/pull/11230>`_, by Jason Gross).
