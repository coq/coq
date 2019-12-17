- **Added:**
  The ``make-both-single-timing-files.py`` script now accepts a
  ``--fuzz=N`` parameter on the command line which determines how many
  characters two lines may be offset in the "before" and "after"
  timing logs while still being considered the same line.  When
  invoking this script via the ``print-pretty-single-time-diff``
  target in a ``Makefile`` made by ``coq_makefile``, you can set this
  argument by passing ``TIMING_FUZZ=N`` to ``make`` (`#11302
  <https://github.com/coq/coq/pull/11302>`_, by Jason Gross).

- **Added:**
  The ``make-one-time-file.py`` and ``make-both-time-files.py``
  scripts now accept a ``--real`` parameter on the command line to
  print real times rather than user times in the tables.  The
  ``make-both-single-timing-files.py`` script accepts a ``--user``
  parameter to use user times.  When invoking these scripts via the
  ``print-pretty-timed`` or ``print-pretty-timed-diff`` or
  ``print-pretty-single-time-diff`` targets in a ``Makefile`` made by
  ``coq_makefile``, you can set this argument by passing
  ``TIMING_REAL=1`` (to pass ``--real``) or ``TIMING_REAL=0`` (to pass
  ``--user``) to ``make`` (`#11302
  <https://github.com/coq/coq/pull/11302>`_, by Jason Gross).

- **Added:**
  Coq's build system now supports both ``TIMING_FUZZ``,
  ``TIMING_SORT_BY``, and ``TIMING_REAL`` just like a ``Makefile``
  made by ``coq_makefile`` (`#11302
  <https://github.com/coq/coq/pull/11302>`_, by Jason Gross).

- **Fixed:**
  The various timing targets for Coq's standard library now correctly
  display and label the "before" and "after" columns, rather than
  mixing them up (`#11302 <https://github.com/coq/coq/pull/11302>`_
  fixes `#11301 <https://github.com/coq/coq/issues/11301>`_, by Jason
  Gross).
