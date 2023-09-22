- **Changed:**
  :tacn:`replace` with `by tac` does not automatically attempt to solve
  the generated equality subgoal using the hypotheses.
  Use `by first [assumption | symmetry;assumption | tac]`
  if you need the previous behaviour
  (`#17964 <https://github.com/coq/coq/pull/17964>`_,
  fixes `#17959 <https://github.com/coq/coq/issues/17959>`_,
  by Gaëtan Gilbert).
