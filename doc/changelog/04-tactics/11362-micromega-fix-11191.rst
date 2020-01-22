- **Fixed:**
  :tacn:`zify` now handles :g:`Z.pow_pos` by default.
  In Coq 8.11, this was the case only when loading module
  :g:`ZifyPow` because this triggered a regression of :tacn:`lia`.
  The regression is now fixed, and the module kept only for compatibility
  (`#11362 <https://github.com/coq/coq/pull/11362>`_,
  fixes `#11191 <https://github.com/coq/coq/issues/11191>`_,
  by Frédéric Besson).
