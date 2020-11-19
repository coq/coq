- **Changed:**
  Redeclaring a notation reactivates also its printing rule; in
  particular a second :cmd:`Import` of the same module reactivates the
  printing rules declared in this module. In theory, this leads to
  changes of behavior for printing. However, this is mitigated in
  general by the adoption in `#12986
  <https://github.com/coq/coq/pull/12986>`_ of a priority given to
  notations which match a larger part of the term to print
  (`#12984 <https://github.com/coq/coq/pull/12984>`_,
  fixes `#7443 <https://github.com/coq/coq/issues/7443>`_
  and `#10824 <https://github.com/coq/coq/issues/10824>`_,
  by Hugo Herbelin).
