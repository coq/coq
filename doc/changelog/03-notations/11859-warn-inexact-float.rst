- **Added:**
  In primitive floats, print a warning when parsing a decimal value
  that is not exactly a binary64 floating-point number.
  For instance, parsing 0.1 will print a warning whereas parsing 0.5 won't.
  (`#11859 <https://github.com/coq/coq/pull/11859>`_,
  by Pierre Roux).
