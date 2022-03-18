- **Fixed:**
  Attempted edits to the processed part of a buffer while
  Coq is busy processing a request are now ignored to
  ensure "processed" highlighting is accurate
  (`#15714 <https://github.com/coq/coq/pull/15714>`_,
  fixes `#15733 <https://github.com/coq/coq/issues/15733>`_
  and `#15675 <https://github.com/coq/coq/issues/15675>`_
  and `#15725 <https://github.com/coq/coq/issues/15725>`_,
  by Jim Fehrle).
