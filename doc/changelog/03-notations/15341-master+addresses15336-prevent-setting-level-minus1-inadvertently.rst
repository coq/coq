- **Changed:**
  Warn about notations that would nominally require to parse an
  expression at a level strictly less than the lower level, that is 0;
  in practice, this was tolerated for parsing (falling back on
  level 0) but was breaking printing
  (`#15341 <https://github.com/coq/coq/pull/15341>`_,
  fixes `#15336 <https://github.com/coq/coq/issues/15336>`_,
  by Hugo Herbelin).
