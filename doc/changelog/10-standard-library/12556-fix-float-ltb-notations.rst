- **Changed:**
  PrimFloat notations now match up with the rest of the standard library: :g:`m
  == n`, :g:`m < n`, and :g:`m <= n` have been replaced with :g:`m =? n`, :g:`m
  <? n`, and :g:`m <=? n`.  The old notations are still available as deprecated
  notations.  Additionally, there is now a
  ``Coq.Floats.PrimFloat.PrimFloatNotations`` module that users can import to
  get the ``PrimFloat`` notations without unqualifying the various primitives
  (`#12556 <https://github.com/coq/coq/pull/12556>`_, fixes `#12454
  <https://github.com/coq/coq/issues/12454>`_, by Jason Gross).
