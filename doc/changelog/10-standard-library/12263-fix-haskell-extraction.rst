- **Fixed:**
  In Haskell extraction with ``ExtrHaskellString``, equality comparisons on
  strings and characters are now guaranteed to be uniquely well-typed, even in
  very polymorphic contexts under ``unsafeCoerce``; this is achieved by adding
  type annotations to the extracted code, and by making ``ExtrHaskellString``
  export ``ExtrHaskellBasic`` (`#12263
  <https://github.com/coq/coq/pull/12263>`_, fixes `#12257
  <https://github.com/coq/coq/issues/12257>`_ and `#12258
  <https://github.com/coq/coq/issues/12258>`_, by Jason Gross).
