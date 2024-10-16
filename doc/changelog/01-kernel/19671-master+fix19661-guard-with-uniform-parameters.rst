- **Fixed:**
  Possible guard checker anomaly on fixpoints containing an inner
  fixpoint that is reducible (because of its main argument reducing to a
  constructor). This is a regression in 8.20
  (`#19671 <https://github.com/coq/coq/pull/19671>`_,
  fixes `#19661 <https://github.com/coq/coq/issues/19661>`_,
  by Hugo Herbelin).
