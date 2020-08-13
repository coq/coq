- **Changed:**
  Int63 notations now match up with the rest of the standard library: :g:`a \%
  m`, :g:`m == n`, :g:`m < n`, :g:`m <= n`, and :g:`m ≤ n` have been replaced
  with :g:`a mod m`, :g:`m =? n`, :g:`m <? n`, :g:`m <=? n`, and :g:`m ≤? n`.
  The old notations are still available as deprecated notations.  Additionally,
  there is now a ``Coq.Numbers.Cyclic.Int63.Int63.Int63Notations`` module that
  users can import to get the ``Int63`` notations without unqualifying the
  various primitives (`#12479 <https://github.com/coq/coq/pull/12479>`_, fixes
  `#12454 <https://github.com/coq/coq/issues/12454>`_, by Jason Gross).
