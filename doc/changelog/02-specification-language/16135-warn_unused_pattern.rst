- **Changed:**
  warning for unused variables in pattern-matching triggers
  even when catching a single case. This warning used to be
  triggered only when the unused variable was catching at least
  two cases (`#16135 <https://github.com/coq/coq/pull/16135>`_,
  by Pierre Roux).
