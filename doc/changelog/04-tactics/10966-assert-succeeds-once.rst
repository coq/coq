- The :tacn:`assert_succeeds` and :tacn:`assert_fails` tactics now
  only run their tactic argument once, even if it has multiple
  successes.  This prevents blow-up and looping from using
  multisuccess tactics with :tacn:`assert_succeeds`.  (`#10966
  <https://github.com/coq/coq/pull/10966>`_ fixes `#10965
  <https://github.com/coq/coq/issues/10965>`_, by Jason Gross).

- The :tacn:`assert_succeeds` and :tacn:`assert_fails` tactics now
  behave correctly when their tactic fully solves the goal.  (`#10966
  <https://github.com/coq/coq/pull/10966>`_ fixes `#9114
  <https://github.com/coq/coq/issues/9114>`_, by Jason Gross).
