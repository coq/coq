- **Fixed:** issues when using ``coq_makefile`` to build targets
  requiring both ``.vo`` and ``.glob`` files (typically documentation
  targets), where ``make`` would run multiple ``coqc`` processes on
  the same source file with racy behaviour (only fixed when using a
  ``make`` supporting "grouped targets" such as GNU Make 4.3) (`#16757
  <https://github.com/coq/coq/pull/16757>`_, by Gaëtan Gilbert).
