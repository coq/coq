- **Fixed:**
  properly delayed variable expansion when `coq_makefile` uses
  the combined rule for `.vo` and `.glob` targets,
  i.e. on GNU Make 4.4 and later.
  (`#18077 <https://github.com/coq/coq/pull/18077>`_,
  fixes `#18076 <https://github.com/coq/coq/issues/18076>`_,
  by Gaëtan Gilbert).
