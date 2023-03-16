- **Added:**
  `coqdoc` handles multiple links to the same source. For
  example when declaring an inductive type `t` all occurences
  of `t` itself and its elimination principles like `t_ind`
  point to its declaration
  (`#17118 <https://github.com/coq/coq/pull/17118>`_,
  by Enrico Tassi).
