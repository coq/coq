- **Fixed:**
  Add support to parse a recursive pattern as a sequence of terms in a
  recursive notation even when this recursive pattern is used in
  position of binders; it was formerly raising an anomaly (`#16937
  <https://github.com/coq/coq/pull/16937>`_, fixes `#12467
  <https://github.com/coq/coq/issues/12467>`_, by Hugo Herbelin).
