- **Added:**
  The ``make-one-time-file.py`` and ``make-both-time-files.py``
  scripts now include peak memory usage information in the tables (can
  be turned off by the ``--no-include-mem`` command-line parameter),
  and a ``--sort-by-mem`` parameter to sort the tables by memory
  rather than time.  When invoking these scripts via the
  ``print-pretty-timed`` or ``print-pretty-timed-diff`` targets in a
  ``Makefile`` made by ``coq_makefile``, you can set this argument by
  passing ``TIMING_INCLUDE_MEM=0`` (to pass ``--no-include-mem``) and
  ``TIMING_SORT_BY_MEM=1`` (to pass ``--sort-by-mem``) to ``make``
  (`#11606 <https://github.com/coq/coq/pull/11606>`_, by Jason Gross).

- **Added:**
  Coq's build system now supports both ``TIMING_INCLUDE_MEM`` and
  ``TIMING_SORT_BY_MEM`` just like a ``Makefile`` made by
  ``coq_makefile`` (`#11606 <https://github.com/coq/coq/pull/11606>`_,
  by Jason Gross).

- **Changed:**
  The sorting order of the timing script ``make-both-time-files.py``
  and the target ``print-pretty-timed-diff`` is now deterministic even
  when the sorting order is ``absolute`` or ``diff``; previously the
  relative ordering of two files with identical times was
  non-deterministic (`#11606
  <https://github.com/coq/coq/pull/11606>`_, by Jason Gross).
