- **Fixed:**
  `zify` / `Z.euclidean_division_equations_cleanup` now no longer instantiates
  dependent hypotheses.  This will by necessity make
  `Z.to_euclidean_division_equations` a bit weaker, but the previous behavior
  was overly sensitive to hypothesis ordering.  See `#17935
  <https://github.com/coq/coq/pull/17935>`_ for a recipe to recapture the power
  of the previous behavior in a more robust albeit slower way (`#17935
  <https://github.com/coq/coq/pull/17935>`_, fixes `#17936
  <https://github.com/coq/coq/issues/17936>`_, by Jason Gross).
