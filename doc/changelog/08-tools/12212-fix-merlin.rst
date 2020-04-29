- **Fixed:**
  The ``.merlin`` target of ``coq_makefile``\-made makefiles is now
  properly ``PHONY``, meaning that it will be rebuilt every time you
  call ``make .merlin``, rather than only when the file did not exist
  (`#PRNUM <https://github.com/coq/coq/pull/12212>`_, by Jason Gross).
