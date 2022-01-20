- **Added:**
  ``Ltac2`` understands :n:`toplevel_selector` and obeys :opt:`Default Goal Selector`.
  Note that ``par:`` is buggy when combined with :tacn:`abstract`. Unlike ``Ltac1`` even ``par: abstract tac`` is not properly treated.
  (`#15378 <https://github.com/coq/coq/pull/15378>`_,
  by Gaëtan Gilbert).
