- **Changed:**
  Notations :g:`<=?` and :g:`<?` from ``Coq.Structures.Orders`` and
  ``Coq.Sorting.Mergesort.NatOrder`` are now at level 70 rather than
  35, so as to be compatible with the notations defined everywhere
  else in the standard library.  This may require re-parenthesizing
  some expressions.  These notations were breaking the ability to
  import modules from the standard library that were otherwise
  compatible (fixes `#11890
  <https://github.com/coq/coq/issues/11890>`_, `#11891
  <https://github.com/coq/coq/pull/11891>`_, by Jason Gross).
