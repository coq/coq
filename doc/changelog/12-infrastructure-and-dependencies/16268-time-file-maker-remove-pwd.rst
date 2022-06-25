- **Changed:**
  Coq Makefile targets `pretty-timed`, `make-pretty-timed`,
  `make-pretty-timed-before`, `make-pretty-timed-after`, `print-pretty-timed`,
  `print-pretty-timed-diff`, `print-pretty-single-time-diff` now generate more
  readable timing tables when absolute paths are used in `_CoqProject` / the
  arguments to `coq_makefile`, by stripping off the absolute prefix
  (`#16268 <https://github.com/coq/coq/pull/16268>`_,
  by Jason Gross).
