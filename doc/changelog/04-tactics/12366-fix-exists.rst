- **Changed:**
  When using :tacn:`exists` or :tacn:`eexists` with multiple arguments,
  the evaluation of arguments and applications of constructors are now interleaved.
  This improves unification in some cases
  (`#12366 <https://github.com/coq/coq/pull/12366>`_,
  fixes `#12365 <https://github.com/coq/coq/issues/12365>`_,
  by Attila Gáspár).
