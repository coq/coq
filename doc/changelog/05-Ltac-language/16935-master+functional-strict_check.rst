- **Changed:**
  In toplevel declarations referring to a quotation, such as
  `ltac:(tac)` or `ltac2:(tac)`, the check that term variables present
  in the tactic have to be bound is now done at declaration time
  rather than execution time; this is a possible source of
  incompatibility, for instance, an expression of the form
  `ltac:(intro H; apply H)` should now be replaced by an expression of
  the form `ltac:(let H := fresh in intro H; apply H)`, etc. (`#16935
  <https://github.com/coq/coq/pull/16935>`_, by Hugo Herbelin).
