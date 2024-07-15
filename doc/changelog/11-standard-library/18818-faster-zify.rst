- **Fixed:**
  :g:`Z.euclidean_division_equations_cleanup` has been reordered so that
  :tacn:`zify` (and :tacn:`lia`, :tacn:`nia`, etc) are no longer as slow when the
  context contains many assumptions of the form :g:`0 <= ... < ...`
  (`#18818 <https://github.com/coq/coq/pull/18818>`_,
  fixes `#18770 <https://github.com/coq/coq/issues/18770>`_,
  by Jason Gross).
