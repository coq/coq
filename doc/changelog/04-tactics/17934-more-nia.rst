- **Changed:**
  When using :g:`Z.to_euclidean_division_equations`, :tacn:`nia` can now relate
  :g:`Z.div`/:g:`Z.modulo` to :g:`Z.quot`/:g:`Z.rem` a bit better, by virtue of being
  noticing when there are two equations of the form ``x = y * q₁ + _`` and
  ``x = y * q₂ + _`` (or minor variations thereof), suggesting that ``q₁ = q₂``.
  Users can replace :g:`Z.to_euclidean_division_equations` with
  :g:`let flags := Z.euclidean_division_equations_flags.default_with Z.euclidean_division_equations_flags.find_duplicate_quotients false in Z.to_euclidean_division_equations_with flags`
  or, using :g:`Import Z.euclidean_division_equations_flags.`, with
  :g:`Z.to_euclidean_division_equations_with ltac:(default_with find_duplicate_quotients false)`
  (`#17934 <https://github.com/coq/coq/pull/17934>`_,
  by Jason Gross).
