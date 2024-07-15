- **Changed:**
  The :tacn:`have` tactic generates a proof term containing an opaque
  constant, as it did up to PR `#15121 <https://github.com/coq/coq/pull/15121>`_
  included in Coq 8.16.0. See the variant `have @H` to generate a (transparent)
  let-in instead (:ref:`generating_let_ssr`).
  (`#18449 <https://github.com/coq/coq/pull/18449>`_,
  fixes `#18017 <https://github.com/coq/coq/issues/18017>`_,
  by Enrico Tassi).
