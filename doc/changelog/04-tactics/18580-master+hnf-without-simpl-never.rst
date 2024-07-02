- **Changed:**

  The reduction tactic :tacn:`hnf` becomes insensitive to the
  :g:`simpl never` status of constants, as prescribed in the reference
  manual; this can exceptionally impact the behavior of :tacn:`intros`
  on goals defining an implicative or universally quantified statement
  by recursion (`#18580 <https://github.com/coq/coq/pull/18580>`_,
  by Hugo Herbelin).
