- **Fixed:**
  Regression in error reporting after :tacn:`case <case (ssreflect)>`.
  A generic error message "Could not fill dependent hole in apply" was
  reported for any error following :tacn:`case <case (ssreflect)>` or
  :tacn:`elim <elim (ssreflect)>`
  (`#12857 <https://github.com/coq/coq/pull/12857>`_,
  fixes `#12837 <https://github.com/coq/coq/issues/12837>`_,
  by Enrico Tassi).
