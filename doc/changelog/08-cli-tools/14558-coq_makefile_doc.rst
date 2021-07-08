- **Changed:**
  Syntax of `_CoqProject` files: `-arg` is now handled by :ref:`coq_makefile
  <coq_makefile>` and not by `make`. Unquoted `#` now start line comments.
  (`#14558 <https://github.com/coq/coq/pull/14558>`_,
  by Columbus240, with help from Jim Fehrle and Enrico Tassi).
- **Removed:**
  These options of :ref:`coq_makefile <coq_makefile>`: `-extra`, `-extra-phony`,
  `-custom`, `-no-install`, `-install`, `-no-opt`, `-byte`.
  Support for subdirectories is also removed.
  (`#14558 <https://github.com/coq/coq/pull/14558>`_,
  by Columbus240, with help from Jim Fehrle and Enrico Tassi).
- **Added**:
  :ref:`coq_makefile <coq_makefile>` now takes the `-docroot` option as alternative to the
  `INSTALLCOQDOCROOT` variable
  (`#14558 <https://github.com/coq/coq/pull/14558>`_,
  by Columbus240, with help from Jim Fehrle and Enrico Tassi).
