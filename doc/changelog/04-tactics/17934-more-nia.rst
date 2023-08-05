- **Changed:**
  When using `Z.to_euclidean_division_equations`, `nia` can now relate
  `Z.div`/`Z.modulo` to `Z.quot`/`Z.rem` a bit better, by virtue of being
  noticing when there are two equations of the form `x = y * q₁ + _` and `x = y
  * q₂ + _` (or minor variations thereof), suggesting that `q₁ = q₂`
  (`#17934 <https://github.com/coq/coq/pull/17934>`_,
  by Jason Gross).
