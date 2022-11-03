- **Changed:**
  When multiple tokens match the beginning of a sequence of characters,
  the longest matching token not cutting a subsequence of contiguous
  letters in the middle is used. Previously, this was only the longest
  matching token. See :ref:`lexical conventions <lexing-unseparated-keywords>`
  for details and examples
  (`#16322 <https://github.com/coq/coq/pull/16322>`_,
  fixes `#4712 <https://github.com/coq/coq/issues/4712>`_,
  by Hugo Herbelin).
