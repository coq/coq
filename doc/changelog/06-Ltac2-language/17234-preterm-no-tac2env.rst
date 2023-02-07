- **Fixed:**
  `preterm` quotations are internalized without access to the Ltac2 environment, which matches the runtime behaviour and provides correct errors when referring to Ltac2 values instead of producing anomalies
  (`#17234 <https://github.com/coq/coq/pull/17234>`_,
  fixes `#17233 <https://github.com/coq/coq/issues/17233>`_,
  by Gaëtan Gilbert).
