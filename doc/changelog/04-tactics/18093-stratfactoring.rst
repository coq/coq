- **Changed:**
  The ``rewstrategy`` argument to ``rewrite_strat`` has been factored into
  levels to make parsing precedence clearer.  As a result, ambiguous syntax
  such as ``rewrite_strat topdown choice id id repeat choice choice id id
  repeat id id`` will no longer parse, instead requiring parentheses to
  disambiguate
  (`#18093 <https://github.com/coq/coq/pull/18093>`_,
  by Jason Gross).
