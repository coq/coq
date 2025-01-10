- **Fixed:**
  `cbn` now considers primitive literals (integers, floats, arrays, strings)
  "constructors", i.e. they now satisfy the `!` modifier in `Arguments`
  (`#20004 <https://github.com/coq/coq/pull/20004>`_,
  fixes `#20003 <https://github.com/coq/coq/issues/20003>`_,
  by Jan-Oliver Kaiser).
