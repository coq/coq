- **Changed:**
  ``coqdep`` now reports an error if files specified on the
  command line don't exist or if it encounters unreadable files.
  Unknown options now generate a warning. Previously these
  conditions were ignored.
  (`#14024 <https://github.com/coq/coq/pull/14024>`_,
  fixes `#14023 <https://github.com/coq/coq/issues/14023>`_,
  by Hendrik Tews).
