- **Changed:**
  ``Ltac2.Control.throw_invalid_argument``,
  ``Ltac2.Control.throw_out_of_bounds``,
  ``Ltac2.Control.assert_valid_argument``, ``Ltac2.Control.assert_bounds``, and
  ``Ltac2.Control.backtrack_tactic_failure`` now take printf formats.  The old
  behavior can be captured for non-literal strings with, e.g.,
  `Control.backtrack_tactic_failure "%s" msg`.
  (`#20186 <https://github.com/coq/coq/pull/20186>`_,
  by Jason Gross).
