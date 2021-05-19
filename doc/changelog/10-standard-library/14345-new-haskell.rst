- **Fixed:**
  Haskell extraction is now compatible with GHC versions >= 9.0.  Some ``#if``
  statements have been added to extract ``unsafeCoerce`` to its new location in
  newer versions of GHC.  (`#14345 <https://github.com/coq/coq/pull/14345>`_,
  fixes `#14256 <https://github.com/coq/coq/issues/14256>`_, by Jason Gross).
