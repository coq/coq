- **Fixed:**
  Running ``make`` in ``test-suite/`` twice (or more) in a row will no longer
  rebuild the ``modules/`` tests on subsequent runs, if they have not been
  modified in the meantime (`#12583 <https://github.com/coq/coq/pull/12583>`_,
  fixes `#12582 <https://github.com/coq/coq/issues/12582>`_, by Jason Gross).
