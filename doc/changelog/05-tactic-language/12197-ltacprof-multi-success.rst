- **Fixed:**
  The :flag:`Ltac Profiling` machinery now correctly handles
  backtracking into multi-success tactics.  The call-counts of some
  tactics are unfortunately inflated by 1, as some tactics are
  implicitly implemented as :g:`tac + fail`, which has two
  entry-points rather than one (Fixes `#12196
  <https://github.com/coq/coq/issues/12196>`_, `#12197
  <https://github.com/coq/coq/pull/12197>`_, by Jason Gross).
