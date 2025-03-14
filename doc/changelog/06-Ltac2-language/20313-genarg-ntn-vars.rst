- **Fixed:**
  Ltac2 in terms in notations is more aware of the notation variables it uses,
  providing early failure when the variable is instantiated with an invalid term,
  preventing a spurious warning when a variable that cannot be instantiated is unused,
  and preventing exponential blowups from copying unused data
  (`#20313 <https://github.com/coq/coq/pull/20313>`_,
  fixes `#17833 <https://github.com/coq/coq/issues/17833>`_
  and `#20188 <https://github.com/coq/coq/issues/20188>`_
  and `#20305 <https://github.com/coq/coq/issues/20305>`_,
  by Gaëtan Gilbert).
