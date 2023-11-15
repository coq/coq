- **Added:**
  Ltac2 supports pattern quotations when building `pattern` values.
  This allows building dynamic patterns, eg `Ltac2 eq_pattern a b := pattern:($pattern:a = $pattern:b)`
  (`#17667 <https://github.com/coq/coq/pull/17667>`_,
  by Gaëtan Gilbert).
