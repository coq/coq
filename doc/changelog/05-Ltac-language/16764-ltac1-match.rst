- **Changed:**
  In :tacn:`match goal`, ``match goal with hyp := body : typ |- _``
  is syntax sugar for  ``match goal with hyp := [ body ] : typ |- _``
  i.e. it matches ``typ`` with the type of the hypothesis
  rather than matching the body as a cast term.
  This transformation used to be done with any kind of cast (e.g. VM cast ``<:``)
  and is now done only for default casts ``:``
  (`#16764 <https://github.com/coq/coq/pull/16764>`_,
  by Gaëtan Gilbert).
