- **Fixed:**
  `multi_match!`, `multi_match! goal` and the underlying
  `Ltac2.Pattern.multi_match0` and `Ltac2.Pattern.multi_goal_match0`
  now preserve exceptions from backtracking after a branch succeeded
  instead of replacing them with `Match_failure`
  (e.g. `multi_match! constr:(tt) with tt => () end; Control.zero Not_found`
  now fails with `Not_found` instead of `Match_failure`)
  (`#17597 <https://github.com/coq/coq/pull/17597>`_,
  fixes `#17594 <https://github.com/coq/coq/issues/17594>`_,
  by Gaëtan Gilbert).
